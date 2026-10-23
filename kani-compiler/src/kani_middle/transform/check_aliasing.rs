// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
//! Instrumentation for the aliasing checks (`-Z aliasing-checks`).
//!
//! The checks implement the rules that Stacked Borrows and Tree Borrows share; the rules
//! themselves live in the Kani library (`kani_core::kani_aliasing`), which tracks the state of one
//! non-deterministically chosen byte. This pass gives the library what it needs:
//!
//! - Every local of reference or raw pointer type gets a ghost local holding its *tag*. Creating
//!   a reference (`&place`, `&mut place`) asks the library for a fresh tag whose parent is the
//!   tag of the pointer `place` goes through. Copies and pointer-to-pointer casts keep the tag;
//!   raw pointers keep the tag of the reference they come from.
//! - Every read or write of a place that goes through a single dereference of a tagged local (or
//!   of a `Box`), and every access to a local whose address is taken, calls the library to check
//!   the access and update the state, and asserts that the access breaks no rule.
//! - Direct calls pass the tags of up to four pointer arguments, and of a returned pointer,
//!   through a small buffer in the library, keyed by an identifier of the callee.
//!
//! Pointers whose provenance this pass does not follow get the *unknown* tag: pointers read from
//! memory (other than through a `Box`), pointers returned by indirect calls, places with several
//! dereferences, integer to pointer casts, and pointer locals whose own address is taken. An
//! access through an unknown tag to the tracked byte fails as an unsupported construct, so that
//! a harness never verifies because of what the checks could not see.
//!
//! Not modelled yet: protectors (function-entry retags), two-phase borrows beyond what the
//! reserved state allows, `UnsafeCell` (references to types that are not `Freeze` keep their
//! parent's tag), accesses to unsized places, deallocation, and memory accessed by intrinsics such
//! as `copy_nonoverlapping`.

use crate::args::ExtraChecks;
use crate::kani_middle::kani_functions::{KaniFunction, KaniModel};
use crate::kani_middle::transform::body::{
    CheckType, InsertPosition, MutableBody, SourceInstruction,
};
use crate::kani_middle::transform::check_uninit::is_harness;
use crate::kani_middle::transform::{TransformPass, TransformationType};
use crate::kani_queries::QueryDb;
use rustc_middle::ty::{TyCtxt, TypingEnv, Unnormalized};
use rustc_public::mir::mono::{Instance, InstanceKind};
use rustc_public::mir::{
    AggregateKind, BinOp, Body, BorrowKind, CastKind, ConstOperand, Local, Mutability,
    NonDivergingIntrinsic, Operand, Place, PointerCoercion, ProjectionElem, RawPtrKind, Rvalue,
    StatementKind, TerminatorKind,
};
use rustc_public::rustc_internal;
use rustc_public::ty::{
    AdtKind, FnDef, GenericArgKind, GenericArgs, MirConst, RigidTy, Span, Ty, UintTy,
};
use rustc_public_bridge::IndexedVal;
use std::collections::hash_map::DefaultHasher;
use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};
use tracing::trace;

/// Tag values shared with `kani_core::kani_aliasing`.
const ROOT_TAG: u8 = 0;
const UNKNOWN_TAG: u8 = u8::MAX;
const ACCESS_INVALIDATED: u8 = 1;
const ACCESS_WRITE_FROZEN: u8 = 2;
const MAX_ARG_TAGS: usize = 4;

const MSG_INVALIDATED: &str = "Undefined Behavior: memory accessed through a reference or pointer \
    whose borrow was invalidated by a conflicting access (aliasing checks)";
const MSG_WRITE_FROZEN: &str = "Undefined Behavior: memory written through a pointer with only \
    read permission, derived from a shared reference or from a mutable reference frozen by a \
    later read through another pointer (aliasing checks)";

/// Top-level pass for the aliasing checks.
#[derive(Debug, Clone)]
pub struct AliasingPass {
    pub check_type: CheckType,
    pub unsupported_check_type: CheckType,
    pub kani_functions: HashMap<KaniFunction, FnDef>,
}

impl TransformPass for AliasingPass {
    fn transformation_type() -> TransformationType
    where
        Self: Sized,
    {
        TransformationType::Instrumentation
    }

    fn is_enabled(&self, query_db: &QueryDb) -> bool
    where
        Self: Sized,
    {
        query_db.args().ub_check.contains(&ExtraChecks::Aliasing)
    }

    fn transform(&mut self, tcx: TyCtxt, body: Body, instance: Instance) -> (bool, Body) {
        trace!(function=?instance.name(), "transform");
        // The library functions of the model, and every other Kani function, are not
        // instrumented; instrumenting the model would recurse.
        if KaniFunction::try_from(instance).is_ok() {
            return (false, body);
        }
        let mut body = MutableBody::from(body);
        let instrumenter = Instrumenter::new(tcx, &body, instance, self);
        instrumenter.run(&mut body, is_harness(instance, tcx));
        (true, body.into())
    }
}

/// One step of a path to a pointer inside a local of aggregate type.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum PathElem {
    Field(usize),
    Downcast(usize),
}

/// A pointer-typed place that has its own tag local: a local, or a field of a local, reached
/// without dereferencing.
type PathKey = (Local, Vec<PathElem>);

/// Bounds on the pointers tracked inside one aggregate local.
const MAX_PATH_DEPTH: usize = 4;
const MAX_PATHS_PER_LOCAL: usize = 16;

/// Where the tag of a pointer comes from.
#[derive(Debug, Clone, Copy)]
enum TagValue {
    Const(u8),
    Local(Local),
}

/// One piece of instrumentation for an instruction.
#[derive(Debug, Clone)]
enum Action {
    /// Check and record an access to `place` through `tag`.
    Access { place: Place, tag: TagValue, is_write: bool },
    /// Check and record an access to `count` values of type `elem` at `ptr`, as memory
    /// intrinsics do.
    AccessCount { ptr: Operand, tag: TagValue, count: Operand, elem: Ty, is_write: bool },
    /// A construct the checks do not support: fail if reached.
    Unsupported { msg: String },
    /// Set a tag local.
    SetTag { tag_local: Local, value: TagValue },
    /// Set several tag locals at once: all values are read before any is written.
    SetTags { assignments: Vec<(Local, TagValue)> },
    /// Create a reference through a pointer tagged `parent`.
    NewBorrow { tag_local: Local, parent: TagValue, is_shared: bool },
    /// Reborrow the dropped place and pass the new tag to the drop glue `callee`.
    DropRetag { parent: TagValue, callee: u64 },
    /// Record the argument tags of a direct call.
    PushCall { callee: u64, tags: Vec<TagValue> },
    /// Record the tag of the returned pointer, and drop the tags of this call.
    Return { tag: TagValue },
    /// Retrieve the tag of the pointer returned by a direct call.
    TakeRet { tag_local: Local, callee: u64 },
}

struct Instrumenter<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    pass: &'a AliasingPass,
    /// The ghost tag local of every pointer-typed local, and of every pointer-typed field of an
    /// aggregate local, whose address is not taken.
    tags: HashMap<PathKey, Local>,
    /// Locals whose address is taken, so that direct accesses to them go through the root tag.
    address_taken: HashSet<Local>,
    /// Identifier of the instrumented function, for passing tags across calls.
    own_id: u64,
    /// Ghost local holding the number of tags in use when the function started, if the
    /// function may create tags (it creates references or calls functions).
    frame_count: Option<Local>,
}

impl<'a, 'tcx> Instrumenter<'a, 'tcx> {
    fn new(
        tcx: TyCtxt<'tcx>,
        body: &MutableBody,
        instance: Instance,
        pass: &'a AliasingPass,
    ) -> Self {
        let mut address_taken = HashSet::new();
        for block in body.blocks() {
            for stmt in &block.statements {
                if let StatementKind::Assign(
                    _,
                    Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place),
                ) = &stmt.kind
                    && !place.projection.iter().any(|elem| matches!(elem, ProjectionElem::Deref))
                {
                    address_taken.insert(place.local);
                }
            }
        }
        Instrumenter {
            tcx,
            pass,
            tags: HashMap::new(),
            address_taken,
            own_id: instance_id(instance),
            frame_count: None,
        }
    }

    fn run(mut self, body: &mut MutableBody, is_harness: bool) {
        let span = body.blocks()[0].terminator.source_info.span;
        // A local whose address is taken can be written through that address, which its tag
        // locals would not see: the pointers it holds have unknown tags.
        let mut paths = vec![];
        for (local, decl) in body.locals().iter().enumerate() {
            if self.address_taken.contains(&local) {
                continue;
            }
            let mut local_paths = vec![];
            self.pointer_paths(decl.ty, vec![], MAX_PATH_DEPTH, &mut local_paths);
            paths.extend(local_paths.into_iter().map(|path| (local, path)));
        }
        for key in paths {
            let tag_local = body.new_local(Ty::unsigned_ty(UintTy::U8), span, Mutability::Mut);
            self.tags.insert(key, tag_local);
        }
        let may_create_tags = body.blocks().iter().any(|block| {
            matches!(block.terminator.kind, TerminatorKind::Call { .. })
                || block
                    .statements
                    .iter()
                    .any(|stmt| matches!(stmt.kind, StatementKind::Assign(_, Rvalue::Ref(..))))
        });
        if may_create_tags {
            self.frame_count =
                Some(body.new_local(Ty::unsigned_ty(UintTy::U8), span, Mutability::Not));
        }

        // Collect the instrumentation of the original instructions, then insert it from the last
        // instruction to the first so that earlier positions stay valid.
        body.split_entry_block();
        let mut work = vec![];
        for (bb, block) in body.blocks().iter().enumerate() {
            for (idx, stmt) in block.statements.iter().enumerate() {
                let actions = self.statement_actions(body, &stmt.kind);
                if !actions.is_empty() {
                    work.push((SourceInstruction::Statement { idx, bb }, actions, vec![]));
                }
            }
            let (before, after) = self.terminator_actions(body, &block.terminator.kind);
            if !before.is_empty() || !after.is_empty() {
                work.push((SourceInstruction::Terminator { bb }, before, after));
            }
        }
        for (mut source, before, after) in work.into_iter().rev() {
            for action in before {
                self.insert(body, action, &mut source, InsertPosition::Before);
            }
            for action in after {
                self.insert(body, action, &mut source, InsertPosition::After);
            }
        }

        // Function entry: the harness sets up the state; every function records the number of
        // tags in use, picks up the tags of its pointer arguments and gives every other pointer
        // local the wildcard tag.
        let mut source = SourceInstruction::Terminator { bb: 0 };
        if is_harness {
            let init = self.model(KaniModel::AliasingInitialize, vec![]);
            let ret = unit_place(body, span);
            body.insert_call(&init, &mut source, InsertPosition::Before, vec![], ret);
        }
        if let Some(frame_count) = self.frame_count {
            let frame_enter = self.model(KaniModel::AliasingFrameEnter, vec![]);
            body.insert_call(
                &frame_enter,
                &mut source,
                InsertPosition::Before,
                vec![],
                Place::from(frame_count),
            );
        }
        let mut has_pointer_args = false;
        for local in 1..=body.arg_count() {
            let Some(&tag_local) = self.tags.get(&(local, vec![])) else { continue };
            has_pointer_args = true;
            let index = local - 1;
            let arg_tag = self.model(KaniModel::AliasingArgTag, vec![]);
            let args = vec![
                body.new_uint_operand(self.own_id as u128, UintTy::U64, span),
                body.new_uint_operand(index as u128, UintTy::Usize, span),
            ];
            body.insert_call(
                &arg_tag,
                &mut source,
                InsertPosition::Before,
                args,
                Place::from(tag_local),
            );
        }
        if has_pointer_args {
            let end_args = self.model(KaniModel::AliasingEndArgs, vec![]);
            let ret = unit_place(body, span);
            body.insert_call(&end_args, &mut source, InsertPosition::Before, vec![], ret);
        }
        let mut keys: Vec<(PathKey, Local)> =
            self.tags.iter().map(|(key, tag)| (key.clone(), *tag)).collect();
        keys.sort();
        for ((local, path), tag_local) in keys {
            if local == 0 || local > body.arg_count() || !path.is_empty() {
                self.insert(
                    body,
                    Action::SetTag { tag_local, value: TagValue::Const(UNKNOWN_TAG) },
                    &mut source,
                    InsertPosition::Before,
                );
            }
        }
    }

    /// The tag to use for an access to `place`, if the access is checked: the tag of the pointer
    /// it goes through, or the root tag for a local whose address is taken.
    fn place_tag(&self, body: &MutableBody, place: &Place) -> Option<TagValue> {
        let Some(first_deref) =
            place.projection.iter().position(|elem| matches!(elem, ProjectionElem::Deref))
        else {
            // No pointer is involved: only a local whose address is taken can be aliased.
            return self.address_taken.contains(&place.local).then_some(TagValue::Const(ROOT_TAG));
        };
        let derefs = place.projection.iter().filter(|e| matches!(e, ProjectionElem::Deref)).count();
        if derefs > 1 {
            // The place goes through a pointer read from memory.
            return Some(TagValue::Const(UNKNOWN_TAG));
        }
        let pointer =
            Place { local: place.local, projection: place.projection[..first_deref].to_vec() };
        if pointer.ty(body.locals()).unwrap().kind().is_box() {
            return Some(TagValue::Const(ROOT_TAG));
        }
        Some(self.key_tag(path_key(&pointer)))
    }

    /// The tag of the pointer at `key`, if it has a tag local.
    fn key_tag(&self, key: Option<PathKey>) -> TagValue {
        key.and_then(|key| self.tags.get(&key))
            .map_or(TagValue::Const(UNKNOWN_TAG), |tag| TagValue::Local(*tag))
    }

    /// The paths to the pointers inside a value of type `ty`, appended to `prefix`.
    fn pointer_paths(
        &self,
        ty: Ty,
        prefix: Vec<PathElem>,
        depth: usize,
        out: &mut Vec<Vec<PathElem>>,
    ) {
        if out.len() >= MAX_PATHS_PER_LOCAL {
            return;
        }
        if is_pointer(ty) {
            out.push(prefix);
            return;
        }
        // A `Box` owns its allocation: dereferencing one always uses the root tag.
        if depth == 0 || ty.kind().is_box() {
            return;
        }
        let internal = rustc_internal::internal(self.tcx, ty);
        let typing_env = TypingEnv::fully_monomorphized();
        let normalize = |field_ty: Unnormalized<'tcx, rustc_middle::ty::Ty<'tcx>>| {
            rustc_internal::stable(self.tcx.normalize_erasing_regions(typing_env, field_ty))
        };
        let mut push = |elems: Vec<PathElem>, field_ty: Ty| {
            let mut path = prefix.clone();
            path.extend(elems);
            self.pointer_paths(field_ty, path, depth - 1, out);
        };
        match internal.kind() {
            rustc_middle::ty::TyKind::Tuple(tys) => {
                for (index, field_ty) in tys.iter().enumerate() {
                    push(vec![PathElem::Field(index)], normalize(Unnormalized::new(field_ty)));
                }
            }
            rustc_middle::ty::TyKind::Adt(def, args) if !def.is_union() => {
                for (variant_index, variant) in def.variants().iter_enumerated() {
                    for (field_index, field) in variant.fields.iter_enumerated() {
                        let mut elems = vec![];
                        if def.is_enum() {
                            elems.push(PathElem::Downcast(variant_index.as_usize()));
                        }
                        elems.push(PathElem::Field(field_index.as_usize()));
                        push(elems, normalize(field.ty(self.tcx, args)));
                    }
                }
            }
            rustc_middle::ty::TyKind::Closure(_, args) => {
                for (index, field_ty) in args.as_closure().upvar_tys().iter().enumerate() {
                    push(vec![PathElem::Field(index)], normalize(Unnormalized::new(field_ty)));
                }
            }
            _ => {}
        }
    }

    /// The tag that the pointer at `suffix` inside the value of `rvalue` has.
    fn rvalue_subtag(&self, rvalue: &Rvalue, suffix: &[PathElem]) -> TagValue {
        let unknown = TagValue::Const(UNKNOWN_TAG);
        match rvalue {
            Rvalue::Use(Operand::Copy(place) | Operand::Move(place), _) => {
                self.key_tag(path_key(place).map(|(local, mut path)| {
                    path.extend_from_slice(suffix);
                    (local, path)
                }))
            }
            Rvalue::Aggregate(kind, operands) => {
                let rest = match (kind, suffix) {
                    (AggregateKind::Adt(def, variant, ..), [PathElem::Downcast(v), rest @ ..])
                        if def.kind() == AdtKind::Enum && variant.to_index() == *v =>
                    {
                        rest
                    }
                    (AggregateKind::Adt(def, ..), rest) if def.kind() == AdtKind::Struct => rest,
                    (AggregateKind::Tuple | AggregateKind::Closure(..), rest) => rest,
                    _ => return unknown,
                };
                let [PathElem::Field(index), rest @ ..] = rest else { return unknown };
                match &operands[*index] {
                    operand if rest.is_empty() => self.operand_tag(operand),
                    Operand::Copy(place) | Operand::Move(place) => {
                        self.key_tag(path_key(place).map(|(local, mut path)| {
                            path.extend_from_slice(rest);
                            (local, path)
                        }))
                    }
                    Operand::Constant(_) | Operand::RuntimeChecks(_) => unknown,
                }
            }
            _ => unknown,
        }
    }

    /// The tag locals of the pointers strictly inside the place `place`.
    fn inner_tags(&self, place: &Place) -> Vec<(Vec<PathElem>, Local)> {
        let Some((local, path)) = path_key(place) else { return vec![] };
        let mut inner: Vec<_> = self
            .tags
            .iter()
            .filter(|((key_local, key_path), _)| {
                *key_local == local && key_path.len() > path.len() && key_path.starts_with(&path)
            })
            .map(|((_, key_path), tag)| (key_path[path.len()..].to_vec(), *tag))
            .collect();
        inner.sort();
        inner
    }

    /// The tag of the pointer an operand evaluates to.
    fn operand_tag(&self, operand: &Operand) -> TagValue {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => self.key_tag(path_key(place)),
            // A constant pointer points to a static or a promoted constant, whose only
            // tag is its root.
            Operand::Constant(_) => TagValue::Const(ROOT_TAG),
            Operand::RuntimeChecks(_) => TagValue::Const(UNKNOWN_TAG),
        }
    }

    /// The tag local of `place`, if it is a pointer with a tag local.
    fn dest_tag(&self, place: &Place) -> Option<Local> {
        path_key(place).and_then(|key| self.tags.get(&key).copied())
    }

    fn read(&self, body: &MutableBody, place: &Place, actions: &mut Vec<Action>) {
        if let Some(tag) = self.place_tag(body, place) {
            actions.push(Action::Access { place: place.clone(), tag, is_write: false });
        }
    }

    fn write(&self, body: &MutableBody, place: &Place, actions: &mut Vec<Action>) {
        if let Some(tag) = self.place_tag(body, place) {
            actions.push(Action::Access { place: place.clone(), tag, is_write: true });
        }
    }

    fn read_operand(&self, body: &MutableBody, operand: &Operand, actions: &mut Vec<Action>) {
        if let Operand::Copy(place) | Operand::Move(place) = operand {
            self.read(body, place, actions);
        }
    }

    /// An access to `count` (or one) values at the pointer `ptr` evaluates to.
    fn access_count(
        &self,
        body: &MutableBody,
        ptr: &Operand,
        count: Option<&Operand>,
        is_write: bool,
        actions: &mut Vec<Action>,
    ) {
        let ptr_ty = ptr.ty(body.locals()).unwrap();
        let Some(elem) = ptr_ty.kind().builtin_deref(true).map(|pointee| pointee.ty) else {
            return;
        };
        if !self.is_sized(elem) {
            actions.push(Action::Unsupported {
                msg: "Kani's aliasing checks do not support memory intrinsics on unsized types"
                    .to_string(),
            });
            return;
        }
        let count = count.cloned().unwrap_or_else(|| {
            Operand::Constant(ConstOperand {
                span: body.blocks()[0].terminator.source_info.span,
                user_ty: None,
                const_: MirConst::try_from_uint(1, UintTy::Usize).unwrap(),
            })
        });
        if ptr_ty.kind().is_ref() && matches!(ptr, Operand::Constant(_)) {
            // A constant reference points to a constant allocation, which no tag can write.
            return;
        }
        let tag = self.operand_tag(ptr);
        actions.push(Action::AccessCount { ptr: ptr.clone(), tag, count, elem, is_write });
    }

    /// The memory accesses of a call to the intrinsic `name`.
    fn intrinsic_accesses(
        &self,
        body: &MutableBody,
        name: &str,
        args: &[Operand],
        actions: &mut Vec<Action>,
    ) {
        match name {
            "copy" | "copy_nonoverlapping" => {
                self.access_count(body, &args[0], Some(&args[2]), false, actions);
                self.access_count(body, &args[1], Some(&args[2]), true, actions);
            }
            "volatile_copy_memory" | "volatile_copy_nonoverlapping_memory" => {
                self.access_count(body, &args[1], Some(&args[2]), false, actions);
                self.access_count(body, &args[0], Some(&args[2]), true, actions);
            }
            "write_bytes" | "volatile_set_memory" => {
                self.access_count(body, &args[0], Some(&args[2]), true, actions);
            }
            "compare_bytes" => {
                self.access_count(body, &args[0], Some(&args[2]), false, actions);
                self.access_count(body, &args[1], Some(&args[2]), false, actions);
            }
            "raw_eq" => {
                self.access_count(body, &args[0], None, false, actions);
                self.access_count(body, &args[1], None, false, actions);
            }
            // A swap reads and writes both sides; the write is the stronger check.
            "typed_swap_nonoverlapping" => {
                self.access_count(body, &args[0], None, true, actions);
                self.access_count(body, &args[1], None, true, actions);
            }
            "volatile_load" | "unaligned_volatile_load" => {
                self.access_count(body, &args[0], None, false, actions);
            }
            "volatile_store" | "unaligned_volatile_store" | "nontemporal_store" => {
                self.access_count(body, &args[0], None, true, actions);
            }
            "simd_gather" | "simd_scatter" | "simd_masked_load" | "simd_masked_store" => {
                actions.push(Action::Unsupported {
                    msg: format!("Kani's aliasing checks do not support the `{name}` intrinsic"),
                });
            }
            _ if name.starts_with("atomic_") && !name.contains("fence") => {
                let is_write = !name.starts_with("atomic_load");
                self.access_count(body, &args[0], None, is_write, actions);
            }
            _ => {}
        }
    }

    fn statement_actions(&self, body: &MutableBody, kind: &StatementKind) -> Vec<Action> {
        let mut actions = vec![];
        match kind {
            StatementKind::Assign(lhs, rvalue) => {
                let dest = self.dest_tag(lhs);
                let mut new_tag = None;
                match rvalue {
                    Rvalue::Ref(_, borrow_kind, place) => {
                        let parent =
                            self.place_tag(body, place).unwrap_or(TagValue::Const(UNKNOWN_TAG));
                        let ty = place.ty(body.locals()).unwrap();
                        let is_shared = matches!(borrow_kind, BorrowKind::Shared);
                        if matches!(borrow_kind, BorrowKind::Fake(_)) {
                            // Only used by the borrow checker: no reference is created.
                            new_tag = Some(parent);
                        } else if is_shared && !self.is_freeze(ty) {
                            // The bytes of an `UnsafeCell` behind a shared reference may be
                            // written, the others not; telling them apart is not modelled yet.
                            new_tag = Some(TagValue::Const(UNKNOWN_TAG));
                        } else {
                            // Creating a reference reads the referenced memory.
                            self.read(body, place, &mut actions);
                            if let Some(tag_local) = dest {
                                actions.push(Action::NewBorrow { tag_local, parent, is_shared });
                            }
                        }
                    }
                    Rvalue::AddressOf(_, place) => {
                        new_tag = Some(
                            self.place_tag(body, place).unwrap_or(TagValue::Const(UNKNOWN_TAG)),
                        );
                    }
                    Rvalue::Use(operand, _) => {
                        self.read_operand(body, operand, &mut actions);
                        new_tag = Some(self.operand_tag(operand));
                    }
                    Rvalue::Cast(cast_kind, operand, _) => {
                        self.read_operand(body, operand, &mut actions);
                        let keeps_provenance = matches!(
                            cast_kind,
                            CastKind::PtrToPtr
                                | CastKind::Subtype
                                | CastKind::Transmute
                                | CastKind::PointerCoercion(
                                    PointerCoercion::MutToConstPointer
                                        | PointerCoercion::ArrayToPointer
                                        | PointerCoercion::Unsize
                                )
                        );
                        new_tag = Some(match cast_kind {
                            // The pointer inside a `Box`, which owns its allocation.
                            CastKind::BoxDerefTransmute => TagValue::Const(ROOT_TAG),
                            _ if keeps_provenance => self.operand_tag(operand),
                            _ => TagValue::Const(UNKNOWN_TAG),
                        });
                    }
                    Rvalue::Reborrow(_, _, place) => {
                        // A bitwise copy of `place`, like a `Use` of it.
                        self.read(body, place, &mut actions);
                        new_tag = Some(self.operand_tag(&Operand::Copy(place.clone())));
                    }
                    Rvalue::CopyForDeref(place) | Rvalue::Discriminant(place) => {
                        self.read(body, place, &mut actions);
                    }
                    Rvalue::BinaryOp(bin_op, lhs_op, rhs_op)
                    | Rvalue::CheckedBinaryOp(bin_op, lhs_op, rhs_op) => {
                        self.read_operand(body, lhs_op, &mut actions);
                        self.read_operand(body, rhs_op, &mut actions);
                        if *bin_op == BinOp::Offset {
                            new_tag = Some(self.operand_tag(lhs_op));
                        }
                    }
                    Rvalue::UnaryOp(_, operand) | Rvalue::Repeat(operand, _) => {
                        self.read_operand(body, operand, &mut actions);
                    }
                    Rvalue::Aggregate(kind, operands) => {
                        for operand in operands {
                            self.read_operand(body, operand, &mut actions);
                        }
                        // A raw pointer built from a data pointer and metadata
                        // (`ptr::from_raw_parts`) has the data pointer's provenance.
                        if matches!(kind, AggregateKind::RawPtr(..)) {
                            new_tag = Some(self.operand_tag(&operands[0]));
                        }
                    }
                    Rvalue::Len(_) | Rvalue::ThreadLocalRef(_) => {}
                }
                self.write(body, lhs, &mut actions);
                if let Some(tag_local) = dest
                    && !actions.iter().any(|a| matches!(a, Action::NewBorrow { .. }))
                {
                    let value = new_tag.unwrap_or(TagValue::Const(UNKNOWN_TAG));
                    actions.push(Action::SetTag { tag_local, value });
                }
                // The pointers inside an aggregate value.
                let assignments: Vec<_> = self
                    .inner_tags(lhs)
                    .into_iter()
                    .map(|(suffix, tag_local)| (tag_local, self.rvalue_subtag(rvalue, &suffix)))
                    .collect();
                if !assignments.is_empty() {
                    actions.push(Action::SetTags { assignments });
                }
            }
            StatementKind::SetDiscriminant { place, .. } => self.write(body, place, &mut actions),
            StatementKind::Intrinsic(NonDivergingIntrinsic::CopyNonOverlapping(copy)) => {
                self.access_count(body, &copy.src, Some(&copy.count), false, &mut actions);
                self.access_count(body, &copy.dst, Some(&copy.count), true, &mut actions);
            }
            StatementKind::FakeRead(..)
            | StatementKind::StorageLive(_)
            | StatementKind::StorageDead(_)
            | StatementKind::PlaceMention(_)
            | StatementKind::AscribeUserType { .. }
            | StatementKind::Coverage(_)
            | StatementKind::Intrinsic(NonDivergingIntrinsic::Assume(_))
            | StatementKind::ConstEvalCounter
            | StatementKind::Nop => {}
        }
        actions
    }

    /// The instrumentation before and after a terminator.
    fn terminator_actions(
        &self,
        body: &MutableBody,
        kind: &TerminatorKind,
    ) -> (Vec<Action>, Vec<Action>) {
        let mut before = vec![];
        let mut after = vec![];
        match kind {
            TerminatorKind::Call { func, args, destination, target, .. } => {
                for arg in args {
                    self.read_operand(body, arg, &mut before);
                }
                if let Some(name) = intrinsic_name(body, func) {
                    self.intrinsic_accesses(body, &name, args, &mut before);
                }
                let callee = direct_callee(body, func).map(instance_id);
                let has_pointer_args =
                    args.iter().any(|arg| is_pointer(arg.ty(body.locals()).unwrap()));
                if let Some(callee) = callee
                    && has_pointer_args
                {
                    let tags =
                        args.iter().take(MAX_ARG_TAGS).map(|arg| self.operand_tag(arg)).collect();
                    before.push(Action::PushCall { callee, tags });
                }
                if target.is_some() {
                    if let Some(tag_local) = self.dest_tag(destination) {
                        after.push(match (callee, provenance_intrinsic(body, func)) {
                            // Pointer arithmetic keeps the provenance of its pointer operand.
                            (_, true) => {
                                Action::SetTag { tag_local, value: self.operand_tag(&args[0]) }
                            }
                            (Some(callee), false) => Action::TakeRet { tag_local, callee },
                            (None, false) => {
                                Action::SetTag { tag_local, value: TagValue::Const(UNKNOWN_TAG) }
                            }
                        });
                    }
                    let assignments: Vec<_> = self
                        .inner_tags(destination)
                        .into_iter()
                        .map(|(_, tag_local)| (tag_local, TagValue::Const(UNKNOWN_TAG)))
                        .collect();
                    if !assignments.is_empty() {
                        after.push(Action::SetTags { assignments });
                    }
                    self.write(body, destination, &mut after);
                }
            }
            TerminatorKind::Drop { place, .. } => {
                // Dropping passes `&mut place` to the drop glue: a reborrow, which reads the
                // place, then a call. The glue's own accesses are checked through the new tag.
                self.read(body, place, &mut before);
                let ty = place.ty(body.locals()).unwrap();
                let drop_glue = Instance::resolve_drop_in_place(ty);
                let parent = self.place_tag(body, place).unwrap_or(TagValue::Const(UNKNOWN_TAG));
                before.push(Action::DropRetag { parent, callee: instance_id(drop_glue) });
            }
            TerminatorKind::SwitchInt { discr: operand, .. }
            | TerminatorKind::Assert { cond: operand, .. } => {
                self.read_operand(body, operand, &mut before)
            }
            TerminatorKind::Return => {
                let tag = self.tags.get(&(0, vec![])).map(|tag| TagValue::Local(*tag));
                if tag.is_some() || self.frame_count.is_some() {
                    let tag = tag.unwrap_or(TagValue::Const(UNKNOWN_TAG));
                    before.push(Action::Return { tag });
                }
            }
            TerminatorKind::Goto { .. }
            | TerminatorKind::Resume
            | TerminatorKind::Abort
            | TerminatorKind::Unreachable
            | TerminatorKind::InlineAsm { .. } => {}
        }
        (before, after)
    }

    fn insert(
        &self,
        body: &mut MutableBody,
        action: Action,
        source: &mut SourceInstruction,
        position: InsertPosition,
    ) {
        let span = source.span(body.blocks());
        match action {
            Action::Access { place, tag, is_write } => {
                let ty = place.ty(body.locals()).unwrap();
                let model = if self.is_sized(ty) {
                    KaniModel::AliasingAccess
                } else {
                    KaniModel::AliasingAccessUnsized
                };
                let ptr = body.insert_assignment(
                    Rvalue::AddressOf(RawPtrKind::Const, place),
                    source,
                    position,
                );
                let code = body.new_local(Ty::unsigned_ty(UintTy::U8), span, Mutability::Not);
                let access = self.model(model, vec![ty]);
                let args = vec![
                    self.tag_operand(body, tag, span),
                    Operand::Move(Place::from(ptr)),
                    bool_operand(is_write, span),
                ];
                body.insert_call(&access, source, position, args, Place::from(code));
                self.insert_access_checks(body, code, is_write, source, position);
            }
            Action::AccessCount { ptr, tag, count, elem, is_write } => {
                let ptr_ty = ptr.ty(body.locals()).unwrap();
                let ptr = if ptr_ty == Ty::new_ptr(elem, Mutability::Not) {
                    ptr
                } else if ptr_ty.kind().is_raw_ptr() {
                    let cast = body.insert_ptr_cast(ptr, elem, Mutability::Not, source, position);
                    Operand::Move(Place::from(cast))
                } else {
                    // A reference: take the address of its referent.
                    let (Operand::Copy(place) | Operand::Move(place)) = ptr else {
                        unreachable!("constant reference passed to a memory intrinsic")
                    };
                    let mut referent = place;
                    referent.projection.push(ProjectionElem::Deref);
                    let raw = body.insert_assignment(
                        Rvalue::AddressOf(RawPtrKind::Const, referent),
                        source,
                        position,
                    );
                    Operand::Move(Place::from(raw))
                };
                let code = body.new_local(Ty::unsigned_ty(UintTy::U8), span, Mutability::Not);
                let access = self.model(KaniModel::AliasingAccessCount, vec![elem]);
                let args = vec![
                    self.tag_operand(body, tag, span),
                    ptr,
                    count,
                    bool_operand(is_write, span),
                ];
                body.insert_call(&access, source, position, args, Place::from(code));
                self.insert_access_checks(body, code, is_write, source, position);
            }
            Action::Unsupported { msg } => {
                body.insert_check(&self.pass.unsupported_check_type, source, position, None, &msg);
            }
            Action::SetTag { tag_local, value } => {
                let operand = self.tag_operand(body, value, span);
                body.assign_to(
                    Place::from(tag_local),
                    Rvalue::Use(operand, rustc_public::mir::WithRetag::No),
                    source,
                    position,
                );
            }
            Action::SetTags { assignments } => {
                // Read every value into a temporary first: the sources may be among the targets.
                let temps: Vec<_> = assignments
                    .iter()
                    .map(|(_, value)| {
                        let operand = self.tag_operand(body, *value, span);
                        body.insert_assignment(
                            Rvalue::Use(operand, rustc_public::mir::WithRetag::No),
                            source,
                            position,
                        )
                    })
                    .collect();
                for ((tag_local, _), temp) in assignments.iter().zip(temps) {
                    body.assign_to(
                        Place::from(*tag_local),
                        Rvalue::Use(
                            Operand::Copy(Place::from(temp)),
                            rustc_public::mir::WithRetag::No,
                        ),
                        source,
                        position,
                    );
                }
            }
            Action::NewBorrow { tag_local, parent, is_shared } => {
                let new_borrow = self.model(KaniModel::AliasingNewBorrow, vec![]);
                let args =
                    vec![self.tag_operand(body, parent, span), bool_operand(is_shared, span)];
                body.insert_call(&new_borrow, source, position, args, Place::from(tag_local));
            }
            Action::DropRetag { parent, callee } => {
                let tag_local = body.new_local(Ty::unsigned_ty(UintTy::U8), span, Mutability::Not);
                let new_borrow = self.model(KaniModel::AliasingNewBorrow, vec![]);
                let args = vec![self.tag_operand(body, parent, span), bool_operand(false, span)];
                body.insert_call(&new_borrow, source, position, args, Place::from(tag_local));
                self.insert(
                    body,
                    Action::PushCall { callee, tags: vec![TagValue::Local(tag_local)] },
                    source,
                    position,
                );
            }
            Action::PushCall { callee, tags } => {
                let push = self.model(KaniModel::AliasingPushCall, vec![]);
                let mut args = vec![body.new_uint_operand(callee as u128, UintTy::U64, span)];
                for index in 0..MAX_ARG_TAGS {
                    let tag = tags.get(index).copied().unwrap_or(TagValue::Const(UNKNOWN_TAG));
                    args.push(self.tag_operand(body, tag, span));
                }
                let ret = unit_place(body, span);
                body.insert_call(&push, source, position, args, ret);
            }
            Action::Return { tag } => {
                let ret_model = self.model(KaniModel::AliasingReturn, vec![]);
                // Without a frame count, the function created no tags: passing the wildcard tag
                // as the count keeps them all.
                let frame_count = match self.frame_count {
                    Some(local) => Operand::Copy(Place::from(local)),
                    None => body.new_uint_operand(UNKNOWN_TAG as u128, UintTy::U8, span),
                };
                let args = vec![
                    body.new_uint_operand(self.own_id as u128, UintTy::U64, span),
                    frame_count,
                    self.tag_operand(body, tag, span),
                ];
                let ret = unit_place(body, span);
                body.insert_call(&ret_model, source, position, args, ret);
            }
            Action::TakeRet { tag_local, callee } => {
                let take_ret = self.model(KaniModel::AliasingTakeRet, vec![]);
                let args = vec![body.new_uint_operand(callee as u128, UintTy::U64, span)];
                body.insert_call(&take_ret, source, position, args, Place::from(tag_local));
            }
        }
    }

    /// Assert that the result of an access breaks no rule.
    fn insert_access_checks(
        &self,
        body: &mut MutableBody,
        code: Local,
        is_write: bool,
        source: &mut SourceInstruction,
        position: InsertPosition,
    ) {
        self.insert_ne_check(body, code, ACCESS_INVALIDATED, MSG_INVALIDATED, source, position);
        if is_write {
            self.insert_ne_check(
                body,
                code,
                ACCESS_WRITE_FROZEN,
                MSG_WRITE_FROZEN,
                source,
                position,
            );
        }
    }

    /// Assert that the `u8` in `value` is not `bad`.
    fn insert_ne_check(
        &self,
        body: &mut MutableBody,
        value: Local,
        bad: u8,
        msg: &str,
        source: &mut SourceInstruction,
        position: InsertPosition,
    ) {
        let span = source.span(body.blocks());
        let bad = body.new_uint_operand(bad as u128, UintTy::U8, span);
        let ok = body.insert_binary_op(
            BinOp::Ne,
            Operand::Copy(Place::from(value)),
            bad,
            source,
            position,
        );
        body.insert_check(&self.pass.check_type, source, position, Some(ok), msg);
    }

    fn tag_operand(&self, body: &mut MutableBody, tag: TagValue, span: Span) -> Operand {
        match tag {
            TagValue::Const(value) => body.new_uint_operand(value as u128, UintTy::U8, span),
            TagValue::Local(local) => Operand::Copy(Place::from(local)),
        }
    }

    fn model(&self, model: KaniModel, tys: Vec<Ty>) -> Instance {
        let def = self.pass.kani_functions[&KaniFunction::Model(model)];
        let args = GenericArgs(tys.into_iter().map(GenericArgKind::Type).collect());
        Instance::resolve(def, &args).unwrap()
    }

    fn is_sized(&self, ty: Ty) -> bool {
        rustc_internal::internal(self.tcx, ty).is_sized(self.tcx, TypingEnv::fully_monomorphized())
    }

    fn is_freeze(&self, ty: Ty) -> bool {
        rustc_internal::internal(self.tcx, ty).is_freeze(self.tcx, TypingEnv::fully_monomorphized())
    }
}

/// The path key of `place`, if it is a local or a field of one, reached without dereferencing.
fn path_key(place: &Place) -> Option<PathKey> {
    let path = place
        .projection
        .iter()
        .map(|elem| match elem {
            ProjectionElem::Field(index, _) => Some(PathElem::Field(*index)),
            ProjectionElem::Downcast(variant) => Some(PathElem::Downcast(variant.to_index())),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()?;
    Some((place.local, path))
}

/// Whether values of `ty` carry a tag: references and raw pointers.
fn is_pointer(ty: Ty) -> bool {
    let kind = ty.kind();
    kind.is_ref() || kind.is_raw_ptr()
}

/// The instance a call calls, if it is a direct call to a function with a body.
fn direct_callee(body: &MutableBody, func: &Operand) -> Option<Instance> {
    let (def, args) = fn_def(body, func)?;
    // Intrinsics are generated by the backend, even those with a fallback body.
    if def.as_intrinsic().is_some() {
        return None;
    }
    let instance = Instance::resolve(def, &args).ok()?;
    matches!(instance.kind, InstanceKind::Item | InstanceKind::Shim).then_some(instance)
}

/// Whether `func` is an intrinsic (or Kani's model of one) that returns a pointer with the
/// provenance of its first argument: the pointer arithmetic behind `ptr::add` and friends, and
/// `aggregate_raw_ptr` behind `ptr::slice_from_raw_parts`.
fn provenance_intrinsic(body: &MutableBody, func: &Operand) -> bool {
    let Some((def, args)) = fn_def(body, func) else { return false };
    // Kani replaces `offset` by its own model before this pass runs.
    if let Ok(instance) = Instance::resolve(def, &args)
        && KaniFunction::try_from(instance) == Ok(KaniFunction::Model(KaniModel::Offset))
    {
        return true;
    }
    let Some(intrinsic) = def.as_intrinsic() else { return false };
    matches!(
        intrinsic.fn_name().as_str(),
        "aggregate_raw_ptr" | "arith_offset" | "offset" | "ptr_mask"
    )
}

/// The name of the intrinsic a call calls, if it calls one.
fn intrinsic_name(body: &MutableBody, func: &Operand) -> Option<String> {
    let (def, _) = fn_def(body, func)?;
    Some(def.as_intrinsic()?.fn_name().to_string())
}

/// The function a call operand names, if it is a function item. Earlier passes call through
/// locals of function item type, so this looks at the operand's type.
fn fn_def(body: &MutableBody, func: &Operand) -> Option<(FnDef, GenericArgs)> {
    let RigidTy::FnDef(def, args) = func.ty(body.locals()).ok()?.kind().rigid()?.clone() else {
        return None;
    };
    Some((def, args))
}

/// A stable identifier of a function instance, for matching callers with callees.
fn instance_id(instance: Instance) -> u64 {
    let mut hasher = DefaultHasher::new();
    instance.mangled_name().hash(&mut hasher);
    // Zero means "no pending call" in the library.
    hasher.finish().max(1)
}

fn bool_operand(value: bool, span: Span) -> Operand {
    Operand::Constant(ConstOperand { span, user_ty: None, const_: MirConst::from_bool(value) })
}

fn unit_place(body: &mut MutableBody, span: Span) -> Place {
    Place::from(body.new_local(Ty::new_tuple(&[]), span, Mutability::Not))
}
