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
//! - A pointer written to memory (through a dereference, or to a local whose address is taken or
//!   that holds pointers in an array) has its tag stored in CBMC's shadow memory, and a pointer
//!   read from memory gets the tag stored there. Every other write to memory forgets the tags in
//!   the words it overwrites; memory intrinsics, which copy bytes without their tags, forget the
//!   tags of the object they write.
//!
//! Loop contracts and C functions write memory without instrumentation: where they may, every
//! stored tag is forgotten.
//!
//! Pointers whose provenance this pass does not follow get the *unknown* tag: pointers read from
//! memory where no tag was stored, pointers returned by indirect calls, and integer to pointer
//! casts.
//! An access through an unknown tag to the tracked byte fails as an unsupported construct, so
//! that a harness never verifies because of what the checks could not see.
//!
//! Not modelled yet: `UnsafeCell` in unsized types, and the tags of pointers that memory
//! intrinsics copy.

use crate::args::ExtraChecks;
use crate::kani_middle::attributes::KaniAttributes;
use crate::kani_middle::kani_functions::{KaniFunction, KaniModel};
use crate::kani_middle::transform::body::{
    CheckType, InsertPosition, MutableBody, SourceInstruction,
};
use crate::kani_middle::transform::check_uninit::{is_harness, raw_ptr_arg};
use crate::kani_middle::transform::{TransformPass, TransformationType};
use crate::kani_queries::QueryDb;
use rustc_middle::ty::{TyCtxt, TypingEnv, Unnormalized};
use rustc_public::CrateDef;
use rustc_public::abi::{FieldsShape, Scalar, TagEncoding, VariantsShape};
use rustc_public::mir::mono::{Instance, InstanceKind};
use rustc_public::mir::{
    AggregateKind, BinOp, Body, BorrowKind, CastKind, ConstOperand, Local, Mutability,
    NonDivergingIntrinsic, Operand, Place, PointerCoercion, ProjectionElem, RawPtrKind, Rvalue,
    StatementKind, TerminatorKind,
};
use rustc_public::rustc_internal;
use rustc_public::target::MachineInfo;
use rustc_public::ty::{
    AdtKind, FnDef, GenericArgKind, GenericArgs, MirConst, RigidTy, Span, Ty, UintTy,
};
use rustc_public_bridge::IndexedVal;
use rustc_span::Symbol;
use std::collections::hash_map::DefaultHasher;
use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};
use tracing::trace;

/// Tag values shared with `kani_core::kani_aliasing`.
const ROOT_TAG: u8 = 0;
const UNKNOWN_TAG: u8 = u8::MAX;
const EXPOSED_TAG: u8 = u8::MAX - 1;
const ACCESS_INVALIDATED: u8 = 1;
const ACCESS_WRITE_FROZEN: u8 = 2;
const ACCESS_PROTECTOR: u8 = 3;
const ACCESS_NOT_EXPOSED: u8 = 4;
const ACCESS_UNKNOWN_TAG: u8 = 5;
const ACCESS_UNKNOWN_EXPOSED: u8 = 6;
const ACCESS_UNKNOWN_WILDCARD: u8 = 7;
const ACCESS_PROTECTED_DEALLOC: u8 = 8;
const MAX_ARG_TAGS: usize = 8;
const MAX_RET_TAGS: usize = 4;

const MSG_INVALIDATED: &str = "Undefined Behavior: memory accessed through a reference or pointer \
    whose borrow was invalidated by a conflicting access (aliasing checks)";
const MSG_PROTECTOR: &str = "Undefined Behavior: memory written while a function runs in a way that \
    invalidates a reference passed to that function, or written through such a reference after a \
    conflicting read (aliasing checks)";
const MSG_DEALLOC_PROTECTED: &str = "Undefined Behavior: memory deallocated while a reference passed \
    to a running function points to it (aliasing checks)";
const MSG_NOT_EXPOSED: &str = "Undefined Behavior: memory accessed through a pointer created from an \
    integer, but no exposed pointer allows this access (aliasing checks)";
/// The results the checks cannot decide, reported as unsupported at the access.
const UNKNOWN_RESULTS: [(u8, &str); 3] = [
    (
        ACCESS_UNKNOWN_TAG,
        "Kani's aliasing checks do not know which reference this pointer was derived from, so \
         they cannot check this access",
    ),
    (
        ACCESS_UNKNOWN_EXPOSED,
        "Kani's aliasing checks cannot check an access through a pointer created from an \
         integer once a pointer whose tag they do not know was exposed",
    ),
    (
        ACCESS_UNKNOWN_WILDCARD,
        "Kani's aliasing checks cannot check this access through pointers created from \
         integers: its result depends on the order in which Tree Borrows visits the exposed \
         pointers",
    ),
];
const MSG_WRITE_FROZEN: &str = "Undefined Behavior: memory written through a pointer with only \
    read permission, derived from a shared reference or from a mutable reference frozen by a \
    later read through another pointer (aliasing checks)";

/// Top-level pass for the aliasing checks.
#[derive(Debug, Clone)]
pub struct AliasingPass {
    pub check_type: CheckType,
    pub unsupported_check_type: CheckType,
    /// The check that an access's result is decided: it fails, and stops the execution, at an
    /// access the checks cannot decide.
    pub unknown_check_type: CheckType,
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
        // Kani functions are not instrumented, nor is any function of the aliasing model's
        // module (its helpers and the monitor have no marker): instrumenting the model would
        // recurse.
        if KaniFunction::try_from(instance).is_ok() || is_aliasing_model(instance) {
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
    /// An element of an array; the pointers in arrays are only tracked in shadow memory.
    Index(usize),
}

/// A pointer-typed place that has its own tag local: a local, or a field of a local, reached
/// without dereferencing.
type PathKey = (Local, Vec<PathElem>);

/// Bounds on the pointers tracked inside one aggregate local.
const MAX_PATH_DEPTH: usize = 8;
const MAX_PATHS_PER_LOCAL: usize = 16;

/// How Miri retags the pointer at a path: a reference, or the pointer inside a `Box`, which is
/// retagged like a mutable reference but only weakly protected.
#[derive(Debug, Clone, Copy)]
struct RetagKind {
    is_shared: bool,
    is_box: bool,
}

/// Where the tag of a pointer comes from.
#[derive(Debug, Clone)]
enum TagValue {
    Const(u8),
    Local(Local),
    /// The tag stored in shadow memory for the pointer at this place in memory.
    Load(Place),
}

/// The enum variants a pointer inside an aggregate is in: an action on it only happens if each
/// place has the variant (its discriminant), as Miri retags only the references of the active
/// variant.
type Guard = Vec<(Place, u128)>;

/// One piece of instrumentation for an instruction.
#[derive(Debug, Clone)]
enum Action {
    /// Check and record an access to `place` through `tag`.
    Access { place: Place, tag: TagValue, is_write: bool, guard: Guard },
    /// Check and record an access to `count` values of type `elem` at `ptr`, as memory
    /// intrinsics do.
    AccessCount { ptr: Operand, tag: TagValue, count: Operand, elem: Ty, is_write: bool },
    /// Check and record an access to the `size` bytes at offset `offset` of `place` through
    /// `tag`: the tag of an enum, which reading or setting its discriminant accesses.
    AccessBytes { place: Place, offset: u64, size: u64, tag: TagValue, is_write: bool },
    /// Record that the pointer tagged `tag` was exposed.
    Expose { tag: TagValue },
    /// Deallocate `size` bytes at `ptr`, tagged `tag`.
    Dealloc { ptr: Operand, tag: TagValue, size: Operand },
    /// A construct the checks do not support: fail if reached.
    Unsupported { msg: String },
    /// Set a tag local.
    SetTag { tag_local: Local, value: TagValue },
    /// Set several tag locals at once: all values are read before any is written.
    SetTags { assignments: Vec<(Local, TagValue)> },
    /// Create a reference through a pointer tagged `parent`; protected for a function's
    /// reference arguments.
    NewBorrow {
        tag_local: Local,
        place: Place,
        parent: TagValue,
        cell_mask: u64,
        is_shared: bool,
        is_protected: bool,
        is_strong: bool,
        guard: Guard,
    },
    /// The read that creating a shared reference to `place` performs, except at the bytes in
    /// `cell_mask`.
    ReadOutsideCells { place: Place, tag: TagValue, cell_mask: u64, guard: Guard },
    /// The protector of the argument tagged by `tag_local` ends.
    EndProtector { tag_local: Local },
    /// Reborrow the dropped place and pass the new tag to the drop glue `callee`.
    DropRetag { place: Place, parent: TagValue, callee: u64 },
    /// The value at `place` in memory was just written: forget the tags stored in its bytes.
    ClearTags { place: Place },
    /// The pointer at `place` in memory was just written: store its tag, if every place of
    /// `guard` has its variant. `outlives_frame` if the memory may outlive the function, so that
    /// the tag must outlive it too.
    StoreTag { place: Place, tag: TagValue, guard: Guard, outlives_frame: bool },
    /// Memory at `ptr` is written without tags: forget every tag stored in its object.
    ForgetTags { ptr: Operand },
    /// Memory may be written without instrumentation: forget every stored tag.
    ForgetAll,
    /// Record the argument tags of a direct call.
    PushCall { callee: u64, tags: Vec<TagValue> },
    /// Record the tag of the returned pointer, and drop the tags of this call.
    Return { tags: Vec<TagValue> },
    /// Retrieve the tag of the pointer returned by a direct call.
    /// `targets` lists, for each tag local, which pointer of the returned value it receives.
    TakeRets { callee: u64, targets: Vec<(usize, Local)> },
}

struct Instrumenter<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    pass: &'a AliasingPass,
    /// The ghost tag local of every pointer-typed local, and of every pointer-typed field of an
    /// aggregate local, whose address is not taken.
    tags: HashMap<PathKey, Local>,
    /// Locals whose address is taken, so that direct accesses to them go through the root tag.
    address_taken: HashSet<Local>,
    /// Locals whose pointers have their tags in shadow memory rather than in tag locals: those
    /// whose address is taken, and those holding pointers in arrays.
    in_memory: HashSet<Local>,
    /// Identifier of the instrumented function, for passing tags across calls.
    own_id: u64,
    /// Ghost local holding the number of tags in use when the function started, if the
    /// function may create tags (it creates references or calls functions).
    frame_count: Option<Local>,
    /// Ghost locals holding the tags of the protected retags of the arguments, in order.
    protector_tags: Vec<Local>,
    /// The locals of the original body, for the types of the places it uses.
    locals: Vec<rustc_public::mir::LocalDecl>,
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
            in_memory: address_taken.clone(),
            address_taken,
            own_id: instance_id(instance),
            frame_count: None,
            protector_tags: vec![],
            locals: body.locals().to_vec(),
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
            if local_paths.iter().flatten().any(|elem| matches!(elem, PathElem::Index(_))) {
                self.in_memory.insert(local);
                continue;
            }
            paths.extend(local_paths.into_iter().map(|path| (local, path)));
        }
        for key in paths {
            let tag_local = body.new_local(Ty::unsigned_ty(UintTy::U8), span, Mutability::Mut);
            self.tags.insert(key, tag_local);
        }
        // The pointers in arguments whose address is taken get their tags in locals at entry,
        // which are then stored in shadow memory.
        let mut entry_tags: HashMap<PathKey, Local> = HashMap::new();
        for local in 1..=body.arg_count() {
            if !self.in_memory.contains(&local) || !self.is_sized(body.locals()[local].ty) {
                continue;
            }
            for path in self.flat_paths(body.locals()[local].ty) {
                let tag_local = body.new_local(Ty::unsigned_ty(UintTy::U8), span, Mutability::Mut);
                entry_tags.insert((local, path), tag_local);
            }
        }
        let arg_tag_local = |tags: &HashMap<PathKey, Local>, key: &PathKey| {
            tags.get(key).or_else(|| entry_tags.get(key)).copied()
        };
        // The pointers in the arguments that are retagged with a protector when the function
        // starts: references and `Box`es, inside aggregates too.
        let mut entry_retags = vec![];
        for local in 1..=body.arg_count() {
            let ty = body.locals()[local].ty;
            for path in self.flat_paths(ty) {
                let Some(tag_local) = arg_tag_local(&self.tags, &(local, path.clone())) else {
                    continue;
                };
                let Some(kind) = self.retag_kind(ty, &path) else { continue };
                let Some((place, guard)) = self.path_place(local, ty, &path) else { continue };
                let protector = body.new_local(Ty::unsigned_ty(UintTy::U8), span, Mutability::Mut);
                entry_retags.push((place, guard, kind, tag_local, protector));
            }
        }
        self.protector_tags = entry_retags.iter().map(|(.., protector)| *protector).collect();
        let may_create_tags = !entry_retags.is_empty()
            || body.blocks().iter().any(|block| {
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
        let blocks = body.blocks().to_vec();
        for (bb, block) in blocks.iter().enumerate() {
            for (idx, stmt) in block.statements.iter().enumerate() {
                let (before, after) = self.statement_actions(body, &stmt.kind);
                if !before.is_empty() || !after.is_empty() {
                    work.push((SourceInstruction::Statement { idx, bb }, before, after));
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
        // local the unknown tag.
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
        // The pointers inside the arguments, in the order the caller lists them.
        let mut has_pointer_args = false;
        let mut slot = 0;
        for local in 1..=body.arg_count() {
            for path in self.flat_paths(body.locals()[local].ty) {
                let index = slot;
                slot += 1;
                if index >= MAX_ARG_TAGS {
                    continue;
                }
                has_pointer_args = true;
                let Some(tag_local) = arg_tag_local(&self.tags, &(local, path)) else { continue };
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
        }
        if has_pointer_args {
            let end_args = self.model(KaniModel::AliasingEndArgs, vec![]);
            let ret = unit_place(body, span);
            body.insert_call(&end_args, &mut source, InsertPosition::Before, vec![], ret);
        }
        // The references and `Box`es in the arguments are retagged when the function starts: a
        // read through the caller's tag, then a child that stays protected until the function
        // returns (strongly for references).
        for (place, guard, kind, tag_local, protector) in entry_retags {
            let actions =
                self.retag(body, &place, kind, TagValue::Local(tag_local), tag_local, true, guard);
            for action in actions {
                self.insert(body, action, &mut source, InsertPosition::Before);
            }
            self.insert(
                body,
                Action::SetTag { tag_local: protector, value: TagValue::Local(tag_local) },
                &mut source,
                InsertPosition::Before,
            );
        }
        // The tags of the arguments whose address is taken go to shadow memory.
        let mut entry_tags: Vec<(PathKey, Local)> = entry_tags.into_iter().collect();
        entry_tags.sort();
        for local in 1..=body.arg_count() {
            let tags: Vec<_> = entry_tags
                .iter()
                .filter(|((key_local, _), _)| *key_local == local)
                .map(|((_, path), tag_local)| (path.clone(), TagValue::Local(*tag_local)))
                .collect();
            if tags.is_empty() {
                continue;
            }
            let mut actions = vec![];
            self.store_tags(&Place::from(local), body.locals()[local].ty, tags, &mut actions);
            for action in actions {
                self.insert(body, action, &mut source, InsertPosition::Before);
            }
        }
        let mut keys: Vec<(PathKey, Local)> =
            self.tags.iter().map(|(key, tag)| (key.clone(), *tag)).collect();
        keys.sort();
        for ((local, _), tag_local) in keys {
            if local == 0 || local > body.arg_count() {
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
        // The last dereference: before it, the place goes through pointers read from memory.
        let Some(last_deref) =
            place.projection.iter().rposition(|elem| matches!(elem, ProjectionElem::Deref))
        else {
            // No pointer is involved: only a local whose address is taken can be aliased.
            return self.address_taken.contains(&place.local).then_some(TagValue::Const(ROOT_TAG));
        };
        let pointer =
            Place { local: place.local, projection: place.projection[..last_deref].to_vec() };
        let pointer_ty = pointer.ty(body.locals()).unwrap();
        // The pointer inside a `Box`, which is where its tag is.
        let suffix = if is_pointer(pointer_ty) {
            vec![]
        } else {
            self.flat_paths(pointer_ty).into_iter().next().unwrap_or_default()
        };
        Some(self.place_ptr_tag(&pointer, &suffix))
    }

    /// The tag of the pointer at `key`, if it has a tag local.
    fn key_tag(&self, key: Option<PathKey>) -> TagValue {
        key.and_then(|key| self.tags.get(&key))
            .map_or(TagValue::Const(UNKNOWN_TAG), |tag| TagValue::Local(*tag))
    }

    /// Whether `place` is in memory, where the tags of the pointers it holds are in shadow
    /// memory: it goes through a dereference, or its local's address is taken.
    fn is_memory(&self, place: &Place) -> bool {
        path_key(place).is_none() || self.in_memory.contains(&place.local)
    }

    /// The tag of the pointer at `suffix` inside `place`: its tag local, or what shadow memory
    /// holds for it.
    fn place_ptr_tag(&self, place: &Place, suffix: &[PathElem]) -> TagValue {
        if !self.is_memory(place) {
            return self.key_tag(path_key(place).map(|(local, mut path)| {
                path.extend_from_slice(suffix);
                (local, path)
            }));
        }
        let Ok(ty) = place.ty(&self.locals) else { return TagValue::Const(UNKNOWN_TAG) };
        match self.path_place_from(place, ty, suffix) {
            // The pointer is only read if it is in the active variants of its enums: the program
            // reads it.
            Some((ptr, _)) => TagValue::Load(ptr),
            None => TagValue::Const(UNKNOWN_TAG),
        }
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
        if depth == 0 {
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
            // A pattern type such as `NonNull`'s `*const T is !null`: its field 0 is the value.
            rustc_middle::ty::TyKind::Pat(inner, _) => {
                push(vec![PathElem::Field(0)], normalize(Unnormalized::new(*inner)));
            }
            rustc_middle::ty::TyKind::Array(elem, len) => {
                let elem = normalize(Unnormalized::new(*elem));
                let len = len.try_to_target_usize(self.tcx).unwrap_or(0);
                for index in 0..len.min(MAX_PATHS_PER_LOCAL as u64) {
                    push(vec![PathElem::Index(index as usize)], elem);
                }
            }
            _ => {}
        }
    }

    /// The type of field `field` of variant `variant` (`None` for a struct, tuple, closure or
    /// pattern type) of `ty`.
    fn field_ty(&self, ty: Ty, variant: Option<usize>, field: usize) -> Option<Ty> {
        let internal = rustc_internal::internal(self.tcx, ty);
        let typing_env = TypingEnv::fully_monomorphized();
        let normalize = |field_ty: Unnormalized<'tcx, rustc_middle::ty::Ty<'tcx>>| {
            rustc_internal::stable(self.tcx.normalize_erasing_regions(typing_env, field_ty))
        };
        match (internal.kind(), variant) {
            (rustc_middle::ty::TyKind::Tuple(tys), None) => {
                tys.get(field).map(|field_ty| normalize(Unnormalized::new(*field_ty)))
            }
            (rustc_middle::ty::TyKind::Adt(def, args), variant) if !def.is_union() => {
                let variant =
                    def.variants().get(rustc_abi::VariantIdx::from_usize(variant.unwrap_or(0)))?;
                let field = variant.fields.get(rustc_abi::FieldIdx::from_usize(field))?;
                Some(normalize(field.ty(self.tcx, args)))
            }
            (rustc_middle::ty::TyKind::Closure(_, args), None) => args
                .as_closure()
                .upvar_tys()
                .get(field)
                .map(|field_ty| normalize(Unnormalized::new(*field_ty))),
            (rustc_middle::ty::TyKind::Pat(inner, _), None) if field == 0 => {
                Some(normalize(Unnormalized::new(*inner)))
            }
            _ => None,
        }
    }

    /// The place of the pointer at `path` inside `local` (of type `ty`), and the enum variants
    /// it is in.
    fn path_place(&self, local: Local, ty: Ty, path: &[PathElem]) -> Option<(Place, Guard)> {
        self.path_place_from(&Place::from(local), ty, path)
    }

    /// The place of the pointer at `path` inside the place `base` (of type `ty`), and the enum
    /// variants inside `base` it is in.
    fn path_place_from(&self, base: &Place, ty: Ty, path: &[PathElem]) -> Option<(Place, Guard)> {
        let local = base.local;
        let mut projection = base.projection.clone();
        let mut guard = vec![];
        let mut ty = ty;
        let mut variant = None;
        for elem in path {
            match elem {
                PathElem::Downcast(index) => {
                    let RigidTy::Adt(def, _) = ty.kind().rigid()?.clone() else { return None };
                    let idx = rustc_public::ty::VariantIdx::to_val(*index);
                    let discr = def.discriminant_for_variant(idx).val;
                    guard.push((Place { local, projection: projection.clone() }, discr));
                    projection.push(ProjectionElem::Downcast(idx));
                    variant = Some(*index);
                }
                PathElem::Field(index) => {
                    ty = self.field_ty(ty, variant.take(), *index)?;
                    projection.push(ProjectionElem::Field(*index, ty));
                }
                PathElem::Index(index) => {
                    let RigidTy::Array(elem, len) = ty.kind().rigid()?.clone() else { return None };
                    let min_length = len.eval_target_usize().ok()?;
                    projection.push(ProjectionElem::ConstantIndex {
                        offset: *index as u64,
                        min_length,
                        from_end: false,
                    });
                    ty = elem;
                }
            }
        }
        Some((Place { local, projection }, guard))
    }

    /// How the pointer at `path` inside a value of type `ty` is retagged, if it is: references,
    /// and the pointer inside a `Box`, whose pointee type is not pinned (Miri does not retag
    /// mutable references and `Box`es to types that are not `Unpin`).
    fn retag_kind(&self, ty: Ty, path: &[PathElem]) -> Option<RetagKind> {
        // The types along the path.
        let mut tys = vec![ty];
        let mut variant = None;
        for elem in path {
            match elem {
                PathElem::Downcast(index) => variant = Some(*index),
                PathElem::Field(index) => {
                    let next = self.field_ty(*tys.last().unwrap(), variant.take(), *index)?;
                    tys.push(next);
                }
                PathElem::Index(_) => {
                    let RigidTy::Array(elem, _) = tys.last().unwrap().kind().rigid()?.clone()
                    else {
                        return None;
                    };
                    tys.push(elem);
                }
            }
        }
        // Miri does not retag inside `MaybeDangling`, `ManuallyDrop` or a coroutine.
        if tys[..tys.len() - 1]
            .iter()
            .any(|ty| rustc_internal::internal(self.tcx, *ty).is_like_maybe_dangling())
        {
            return None;
        }
        let leaf = *tys.last().unwrap();
        let (pointee, kind) = if let Some(pointee) =
            leaf.kind().is_ref().then(|| leaf.kind().builtin_deref(true)).flatten()
        {
            let is_shared = pointee.mutability == Mutability::Not;
            (pointee.ty, RetagKind { is_shared, is_box: false })
        } else {
            // The raw pointer inside a `Box`: `Box.0: Unique`, `Unique.0: NonNull`,
            // `NonNull.0: pattern type`, field 0 of which is the pointer.
            let n = tys.len();
            if n < 5 || !tys[n - 5].kind().is_box() || !leaf.kind().is_raw_ptr() {
                return None;
            }
            let pointee = leaf.kind().builtin_deref(true)?.ty;
            (pointee, RetagKind { is_shared: false, is_box: true })
        };
        if !kind.is_shared && !self.is_unpin(pointee) {
            return None;
        }
        Some(kind)
    }

    /// The bytes of a value of type `ty` that are inside an `UnsafeCell`, as a mask over its first
    /// 64 bytes, or `None` if the layout is not one the checks can describe (an enum or a union
    /// containing an `UnsafeCell`, or one past byte 64).
    fn cell_mask(&self, ty: Ty) -> Option<u64> {
        let mut mask = 0;
        self.cell_bytes(ty, 0, &mut mask).then_some(mask)
    }

    fn cell_bytes(&self, ty: Ty, base: usize, mask: &mut u64) -> bool {
        if self.is_freeze(ty) {
            return true;
        }
        let Ok(layout) = ty.layout() else { return false };
        let layout = layout.shape();
        let internal = rustc_internal::internal(self.tcx, ty);
        if let rustc_middle::ty::TyKind::Adt(def, _) = internal.kind()
            && def.is_unsafe_cell()
        {
            let end = base + layout.size.bytes();
            if end > 64 {
                return false;
            }
            for byte in base..end {
                *mask |= 1 << byte;
            }
            return true;
        }
        match (&layout.fields, self.struct_field_tys(ty)) {
            (FieldsShape::Arbitrary { offsets }, Some(field_tys))
                if offsets.len() == field_tys.len() =>
            {
                offsets.iter().zip(field_tys).all(|(offset, field_ty)| {
                    self.cell_bytes(field_ty, base + offset.bytes(), mask)
                })
            }
            (FieldsShape::Array { stride, count }, _) => {
                let RigidTy::Array(elem, _) = ty.kind().rigid().unwrap().clone() else {
                    return false;
                };
                (0..*count as usize)
                    .all(|index| self.cell_bytes(elem, base + index * stride.bytes(), mask))
            }
            _ => false,
        }
    }

    /// The field types of a struct, tuple or closure type.
    fn struct_field_tys(&self, ty: Ty) -> Option<Vec<Ty>> {
        let internal = rustc_internal::internal(self.tcx, ty);
        let typing_env = TypingEnv::fully_monomorphized();
        let normalize = |field_ty: Unnormalized<'tcx, rustc_middle::ty::Ty<'tcx>>| {
            rustc_internal::stable(self.tcx.normalize_erasing_regions(typing_env, field_ty))
        };
        match internal.kind() {
            rustc_middle::ty::TyKind::Tuple(tys) => {
                Some(tys.iter().map(|field_ty| normalize(Unnormalized::new(field_ty))).collect())
            }
            rustc_middle::ty::TyKind::Adt(def, args) if def.is_struct() => Some(
                def.non_enum_variant()
                    .fields
                    .iter()
                    .map(|field| normalize(field.ty(self.tcx, args)))
                    .collect(),
            ),
            rustc_middle::ty::TyKind::Closure(_, args) => Some(
                args.as_closure()
                    .upvar_tys()
                    .iter()
                    .map(|field_ty| normalize(Unnormalized::new(field_ty)))
                    .collect(),
            ),
            _ => None,
        }
    }

    /// The paths to the pointers inside a value of type `ty`, in the order in which calls pass
    /// their tags. The caller and the callee compute it from the same type.
    fn flat_paths(&self, ty: Ty) -> Vec<Vec<PathElem>> {
        let mut paths = vec![];
        self.pointer_paths(ty, vec![], MAX_PATH_DEPTH, &mut paths);
        paths
    }

    /// The tag of the pointer at `path` inside the value of `operand`.
    fn operand_subtag(&self, operand: &Operand, path: &[PathElem]) -> TagValue {
        if path.is_empty() {
            return self.operand_tag(operand);
        }
        match operand {
            Operand::Copy(place) | Operand::Move(place) => self.place_ptr_tag(place, path),
            Operand::Constant(_) | Operand::RuntimeChecks(_) => TagValue::Const(UNKNOWN_TAG),
        }
    }

    /// The tag that the pointer at `suffix` inside the value of `rvalue`, of type `ty`, has.
    fn rvalue_subtag(&self, rvalue: &Rvalue, ty: Ty, suffix: &[PathElem]) -> TagValue {
        let unknown = TagValue::Const(UNKNOWN_TAG);
        match rvalue {
            // A cast to a newtype around a single pointer, such as `NonNull`, keeps the
            // provenance of the pointer it casts; so does unsizing a `Box`.
            Rvalue::Cast(
                CastKind::Transmute
                | CastKind::PtrToPtr
                | CastKind::Subtype
                | CastKind::PointerCoercion(PointerCoercion::Unsize),
                operand,
                _,
            ) if self.flat_paths(ty).as_slice() == [suffix.to_vec()] => self.operand_tag(operand),
            Rvalue::Use(Operand::Copy(place) | Operand::Move(place), _) => {
                self.place_ptr_tag(place, suffix)
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
                    (AggregateKind::Array(_), [PathElem::Index(index), rest @ ..]) => {
                        return match &operands[*index] {
                            operand if rest.is_empty() => self.operand_tag(operand),
                            Operand::Copy(place) | Operand::Move(place) => {
                                self.place_ptr_tag(place, rest)
                            }
                            Operand::Constant(_) | Operand::RuntimeChecks(_) => unknown,
                        };
                    }
                    _ => return unknown,
                };
                let [PathElem::Field(index), rest @ ..] = rest else { return unknown };
                match &operands[*index] {
                    operand if rest.is_empty() => self.operand_tag(operand),
                    Operand::Copy(place) | Operand::Move(place) => self.place_ptr_tag(place, rest),
                    Operand::Constant(_) | Operand::RuntimeChecks(_) => unknown,
                }
            }
            Rvalue::Repeat(operand, _) => match suffix {
                [PathElem::Index(_)] => self.operand_tag(operand),
                [PathElem::Index(_), rest @ ..] => self.operand_subtag(operand, rest),
                _ => unknown,
            },
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

    /// The tag of the pointer an operand evaluates to: a pointer, or a newtype around one such
    /// as `NonNull` or `Box`.
    fn operand_tag(&self, operand: &Operand) -> TagValue {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                let mut suffix = vec![];
                if let Ok(ty) = place.ty(&self.locals)
                    && !is_pointer(ty)
                    && let [inner] = self.flat_paths(ty).as_slice()
                {
                    suffix.extend_from_slice(inner);
                }
                self.place_ptr_tag(place, &suffix)
            }
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
            actions.push(Action::Access {
                place: place.clone(),
                tag,
                is_write: false,
                guard: vec![],
            });
        }
    }

    fn write(&self, body: &MutableBody, place: &Place, actions: &mut Vec<Action>) {
        if let Some(tag) = self.place_tag(body, place) {
            actions.push(Action::Access {
                place: place.clone(),
                tag,
                is_write: true,
                guard: vec![],
            });
        }
    }

    fn read_operand(&self, body: &MutableBody, operand: &Operand, actions: &mut Vec<Action>) {
        if let Operand::Copy(place) | Operand::Move(place) = operand {
            self.read(body, place, actions);
        }
    }

    /// The instrumentation of a retag of the pointer at `ptr` (a reference, or the pointer inside
    /// a `Box`), tagged `parent`, whose new tag goes to `dest`.
    #[allow(clippy::too_many_arguments)]
    fn retag(
        &self,
        body: &MutableBody,
        ptr: &Place,
        kind: RetagKind,
        parent: TagValue,
        dest: Local,
        is_protected: bool,
        guard: Guard,
    ) -> Vec<Action> {
        let mut referent = ptr.clone();
        referent.projection.push(ProjectionElem::Deref);
        self.reborrow(
            body,
            &referent,
            parent,
            Some(dest),
            kind.is_shared,
            is_protected,
            !kind.is_box,
            guard,
        )
    }

    /// The instrumentation of a reborrow of `place`, reached through a pointer tagged `parent`,
    /// whose tag goes to `dest`.
    #[allow(clippy::too_many_arguments)]
    fn reborrow(
        &self,
        body: &MutableBody,
        place: &Place,
        parent: TagValue,
        dest: Option<Local>,
        is_shared: bool,
        is_protected: bool,
        is_strong: bool,
        guard: Guard,
    ) -> Vec<Action> {
        let ty = place.ty(body.locals()).unwrap();
        let mut actions = vec![];
        let cell_mask = if self.is_freeze(ty) {
            0
        } else if let Some(mask) = self.is_sized(ty).then(|| self.cell_mask(ty)).flatten() {
            mask
        } else if is_shared {
            // A shared reference may write the cell's bytes and not the others; without their
            // layout, the checks cannot tell which.
            if let Some(tag_local) = dest {
                actions.push(Action::SetTag { tag_local, value: TagValue::Const(UNKNOWN_TAG) });
            }
            return actions;
        } else {
            // Treating the cell's bytes like the others only rejects more programs.
            0
        };
        // Creating a reference reads the referenced memory, except a shared reference's cells.
        if is_shared && cell_mask != 0 {
            actions.push(Action::ReadOutsideCells {
                place: place.clone(),
                tag: parent.clone(),
                cell_mask,
                guard: guard.clone(),
            });
        } else {
            self.read(body, place, &mut actions);
            if let Some(Action::Access { tag, guard: access_guard, .. }) = actions.last_mut() {
                *tag = parent.clone();
                *access_guard = guard.clone();
            }
        }
        if let Some(tag_local) = dest {
            actions.push(Action::NewBorrow {
                tag_local,
                place: place.clone(),
                parent,
                cell_mask,
                is_shared,
                is_protected,
                is_strong,
                guard,
            });
        }
        actions
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
        if is_write {
            // The intrinsic writes memory without shadow memory.
            actions.push(Action::ForgetTags { ptr: ptr.clone() });
        }
    }

    /// A memory intrinsic that copies one value of a sized type from each `src` to its `dst`
    /// (`count` is one or absent) moves the tags of the pointers in it, as copying bytes keeps
    /// their provenance: instead of forgetting the tags of the objects it writes, read the tags
    /// at each `src` before the call and store them at each `dst` after it.
    fn transfer_tags(
        &self,
        body: &mut MutableBody,
        pairs: &[(&Operand, &Operand)],
        count: Option<&Operand>,
        before: &mut Vec<Action>,
        after: &mut Vec<Action>,
    ) {
        if let Some(count) = count {
            let Operand::Constant(constant) = count else { return };
            if constant.const_.eval_target_usize() != Ok(1) {
                return;
            }
        }
        let referent = |operand: &Operand| -> Option<(Place, Ty)> {
            let (Operand::Copy(place) | Operand::Move(place)) = operand else { return None };
            let ty = place.ty(body.locals()).ok()?;
            let pointee = ty.kind().builtin_deref(true)?.ty;
            let mut referent = place.clone();
            referent.projection.push(ProjectionElem::Deref);
            Some((referent, pointee))
        };
        let mut moves = vec![];
        for (src, dst) in pairs {
            let (Some((src_place, ty)), Some((dst_place, _))) = (referent(src), referent(dst))
            else {
                return;
            };
            if !self.is_sized(ty) {
                return;
            }
            moves.push((src_place, dst_place, ty, *dst));
        }
        // Read every tag before the call, which may overwrite them.
        let mut stores = vec![];
        for (src_place, dst_place, ty, dst) in moves {
            let mut tags = vec![];
            for suffix in self.flat_paths(ty) {
                let tag = match self.path_place_from(&src_place, ty, &suffix) {
                    Some((ptr, _)) => TagValue::Load(ptr),
                    None => TagValue::Const(UNKNOWN_TAG),
                };
                tags.push((suffix, self.read_tag_before(body, tag, before)));
            }
            stores.push((dst_place, ty, tags, dst.clone()));
        }
        for (dst_place, ty, tags, dst) in stores {
            before.retain(|action| !matches!(action, Action::ForgetTags { ptr } if *ptr == dst));
            self.store_tags(&dst_place, ty, tags, after);
        }
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

    /// A tag that does not depend on memory written later: a tag loaded from shadow memory is
    /// read into a new local by `actions`.
    fn read_tag_before(
        &self,
        body: &mut MutableBody,
        tag: TagValue,
        actions: &mut Vec<Action>,
    ) -> TagValue {
        if !matches!(tag, TagValue::Load(_)) {
            return tag;
        }
        let span = body.blocks()[0].terminator.source_info.span;
        let tag_local = body.new_local(Ty::unsigned_ty(UintTy::U8), span, Mutability::Mut);
        actions.push(Action::SetTag { tag_local, value: tag });
        TagValue::Local(tag_local)
    }

    /// The instrumentation after a write of a value of type `ty` to `place` in memory: forget the
    /// tags in its bytes, then store the tags of the pointers it holds (`tags`, by path).
    fn store_tags(
        &self,
        place: &Place,
        ty: Ty,
        tags: Vec<(Vec<PathElem>, TagValue)>,
        after: &mut Vec<Action>,
    ) {
        after.push(Action::ClearTags { place: place.clone() });
        for (suffix, tag) in tags {
            if matches!(tag, TagValue::Const(UNKNOWN_TAG)) {
                continue;
            }
            if let Some((ptr, guard)) = self.path_place_from(place, ty, &suffix) {
                // A local of this function dies with it, and so may the tags stored in it.
                let outlives_frame =
                    ptr.projection.iter().any(|elem| matches!(elem, ProjectionElem::Deref));
                after.push(Action::StoreTag { place: ptr, tag, guard, outlives_frame });
            }
        }
    }

    /// The instrumentation before and after a statement.
    fn statement_actions(
        &self,
        body: &mut MutableBody,
        kind: &StatementKind,
    ) -> (Vec<Action>, Vec<Action>) {
        let mut actions = vec![];
        let mut after = vec![];
        match kind {
            StatementKind::Assign(lhs, rvalue) => {
                let lhs_ty = lhs.ty(body.locals()).unwrap();
                // A write to memory stores the tags of the pointers it writes in shadow memory.
                let stores_tags = self.is_memory(lhs) && self.is_sized(lhs_ty);
                let span = body.blocks()[0].terminator.source_info.span;
                let dest = if stores_tags && is_pointer(lhs_ty) {
                    Some(body.new_local(Ty::unsigned_ty(UintTy::U8), span, Mutability::Mut))
                } else {
                    self.dest_tag(lhs)
                };
                let mut new_tag = None;
                match rvalue {
                    Rvalue::Ref(_, borrow_kind, place) => {
                        let parent =
                            self.place_tag(body, place).unwrap_or(TagValue::Const(UNKNOWN_TAG));
                        let is_shared = matches!(borrow_kind, BorrowKind::Shared);
                        let ty = place.ty(body.locals()).unwrap();
                        if matches!(borrow_kind, BorrowKind::Fake(_))
                            || (!is_shared && !self.is_unpin(ty))
                        {
                            // A fake borrow is only used by the borrow checker, and Miri does not
                            // retag a mutable reference to a type that is not `Unpin`: no new
                            // tag.
                            new_tag = Some(parent);
                        } else {
                            actions.extend(self.reborrow(
                                body,
                                place,
                                parent,
                                dest,
                                is_shared,
                                false,
                                true,
                                vec![],
                            ));
                        }
                    }
                    Rvalue::AddressOf(_, place) => {
                        new_tag = Some(
                            self.place_tag(body, place).unwrap_or(TagValue::Const(UNKNOWN_TAG)),
                        );
                    }
                    Rvalue::Use(operand, with_retag) => {
                        self.read_operand(body, operand, &mut actions);
                        new_tag = Some(self.operand_tag(operand));
                        // Miri retags the references and `Box`es in a value copied with a
                        // retag, once it is in its place.
                        if matches!(with_retag, rustc_public::mir::WithRetag::Yes)
                            && let Some((local, prefix)) = path_key(lhs)
                        {
                            let lhs_ty = lhs.ty(body.locals()).unwrap();
                            for suffix in self.flat_paths(lhs_ty) {
                                let mut full = prefix.clone();
                                full.extend_from_slice(&suffix);
                                let Some(&tag_local) = self.tags.get(&(local, full)) else {
                                    continue;
                                };
                                let Some(kind) = self.retag_kind(lhs_ty, &suffix) else {
                                    continue;
                                };
                                let Some((ptr, guard)) = self.path_place_from(lhs, lhs_ty, &suffix)
                                else {
                                    continue;
                                };
                                after.extend(self.retag(
                                    body,
                                    &ptr,
                                    kind,
                                    TagValue::Local(tag_local),
                                    tag_local,
                                    false,
                                    guard,
                                ));
                            }
                        }
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
                        if matches!(cast_kind, CastKind::PointerExposeAddress) {
                            actions.push(Action::Expose { tag: self.operand_tag(operand) });
                        }
                        new_tag = Some(match cast_kind {
                            // The pointer inside a `Box`.
                            CastKind::BoxDerefTransmute => self.operand_tag(operand),
                            // Any exposed tag.
                            CastKind::PointerWithExposedProvenance => TagValue::Const(EXPOSED_TAG),
                            _ if keeps_provenance => self.operand_tag(operand),
                            _ => TagValue::Const(UNKNOWN_TAG),
                        });
                    }
                    Rvalue::Reborrow(_, _, place) => {
                        // A bitwise copy of `place`, like a `Use` of it.
                        self.read(body, place, &mut actions);
                        new_tag = Some(self.operand_tag(&Operand::Copy(place.clone())));
                    }
                    Rvalue::CopyForDeref(place) => {
                        self.read(body, place, &mut actions);
                        new_tag = Some(self.operand_tag(&Operand::Copy(place.clone())));
                    }
                    Rvalue::Discriminant(place) => {
                        // Reading the discriminant reads the tag, not the whole value.
                        let ty = place.ty(body.locals()).unwrap();
                        if let Some(tag) = self.place_tag(body, place)
                            && let Some((offset, size, _)) = enum_tag_bytes(ty)
                        {
                            actions.push(Action::AccessBytes {
                                place: place.clone(),
                                offset,
                                size,
                                tag,
                                is_write: false,
                            });
                        }
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
                    .map(|(suffix, tag_local)| {
                        let ty = lhs.ty(body.locals()).unwrap();
                        (tag_local, self.rvalue_subtag(rvalue, ty, &suffix))
                    })
                    .collect();
                if !assignments.is_empty() {
                    actions.push(Action::SetTags { assignments });
                }
                if stores_tags {
                    // The tags are read before the write, which may overwrite where they are.
                    let mut tags = vec![];
                    for suffix in self.flat_paths(lhs_ty) {
                        let tag = if suffix.is_empty() {
                            TagValue::Local(dest.unwrap())
                        } else {
                            self.rvalue_subtag(rvalue, lhs_ty, &suffix)
                        };
                        let mut tag = self.read_tag_before(body, tag, &mut actions);
                        // Miri retags the references and `Box`es in a value copied with a retag:
                        // the new tag is the one stored.
                        if matches!(rvalue, Rvalue::Use(_, rustc_public::mir::WithRetag::Yes))
                            && let Some(kind) = self.retag_kind(lhs_ty, &suffix)
                            && let Some((ptr, guard)) = self.path_place_from(lhs, lhs_ty, &suffix)
                        {
                            let new_tag =
                                body.new_local(Ty::unsigned_ty(UintTy::U8), span, Mutability::Mut);
                            after.extend(self.retag(body, &ptr, kind, tag, new_tag, false, guard));
                            tag = TagValue::Local(new_tag);
                        }
                        tags.push((suffix, tag));
                    }
                    self.store_tags(lhs, lhs_ty, tags, &mut after);
                }
            }
            StatementKind::SetDiscriminant { place, variant_index } => {
                // Setting the discriminant writes the tag, unless the variant is the one a niche
                // does not encode.
                let ty = place.ty(body.locals()).unwrap();
                if let Some(tag) = self.place_tag(body, place)
                    && let Some((offset, size, untagged)) = enum_tag_bytes(ty)
                    && untagged != Some(*variant_index)
                {
                    actions.push(Action::AccessBytes {
                        place: place.clone(),
                        offset,
                        size,
                        tag,
                        is_write: true,
                    });
                }
            }
            StatementKind::Intrinsic(NonDivergingIntrinsic::CopyNonOverlapping(copy)) => {
                self.access_count(body, &copy.src, Some(&copy.count), false, &mut actions);
                self.access_count(body, &copy.dst, Some(&copy.count), true, &mut actions);
                self.transfer_tags(
                    body,
                    &[(&copy.src, &copy.dst)],
                    Some(&copy.count),
                    &mut actions,
                    &mut after,
                );
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
        (actions, after)
    }

    /// The instrumentation before and after a terminator.
    fn terminator_actions(
        &self,
        body: &mut MutableBody,
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
                    match name.as_str() {
                        "copy" | "copy_nonoverlapping" => self.transfer_tags(
                            body,
                            &[(&args[0], &args[1])],
                            Some(&args[2]),
                            &mut before,
                            &mut after,
                        ),
                        "typed_swap_nonoverlapping" => self.transfer_tags(
                            body,
                            &[(&args[0], &args[1]), (&args[1], &args[0])],
                            None,
                            &mut before,
                            &mut after,
                        ),
                        _ => {}
                    }
                }
                // CBMC havocs what a loop contract assigns when the loop starts, after its head
                // registers the contract; a C function may write any memory.
                let writes_uninstrumented =
                    fn_def(body, func).is_some_and(|(def, _)| {
                        KaniAttributes::for_def_id(self.tcx, def.def_id()).fn_marker()
                            == Some(Symbol::intern("kani_register_loop_contract"))
                    }) || direct_callee(body, func).is_some_and(|instance| {
                        instance.is_foreign_item()
                            && !instance.name().starts_with("alloc::alloc::__rust_")
                    });
                if writes_uninstrumented {
                    before.push(Action::ForgetAll);
                    if target.is_some() {
                        after.push(Action::ForgetAll);
                    }
                }
                if let Some(instance) = direct_callee(body, func)
                    && instance.is_foreign_item()
                    && matches!(
                        instance.name().as_str(),
                        "alloc::alloc::__rust_dealloc" | "alloc::alloc::__rust_realloc"
                    )
                {
                    before.push(Action::Dealloc {
                        ptr: raw_ptr_arg(&args[0], body.locals()),
                        tag: self.operand_tag(&args[0]),
                        size: args[1].clone(),
                    });
                }
                let callee = direct_callee(body, func).map(instance_id);
                let tags: Vec<_> = args
                    .iter()
                    .flat_map(|arg| {
                        self.flat_paths(arg.ty(body.locals()).unwrap())
                            .into_iter()
                            .map(move |path| self.operand_subtag(arg, &path))
                    })
                    .take(MAX_ARG_TAGS)
                    .collect();
                if let Some(callee) = callee
                    && !tags.is_empty()
                {
                    before.push(Action::PushCall { callee, tags });
                }
                if target.is_some() {
                    let is_allocator = direct_callee(body, func).is_some_and(|instance| {
                        instance.is_foreign_item()
                            && matches!(
                                instance.name().as_str(),
                                "alloc::alloc::__rust_alloc"
                                    | "alloc::alloc::__rust_alloc_zeroed"
                                    | "alloc::alloc::__rust_realloc"
                            )
                    });
                    let dest_ty = destination.ty(body.locals()).unwrap();
                    let targets: Vec<(usize, Local)> = path_key(destination)
                        .map(|(local, prefix)| {
                            self.flat_paths(dest_ty)
                                .into_iter()
                                .enumerate()
                                .filter_map(|(index, path)| {
                                    let mut full = prefix.clone();
                                    full.extend(path);
                                    self.tags.get(&(local, full)).map(|tag| (index, *tag))
                                })
                                .collect()
                        })
                        .unwrap_or_default();
                    if let Some(tag_local) = self.dest_tag(destination)
                        && (is_allocator || provenance_intrinsic(body, func))
                    {
                        // A new allocation has the allocation's root tag; pointer arithmetic
                        // keeps the provenance of its pointer operand.
                        let value = if is_allocator {
                            TagValue::Const(ROOT_TAG)
                        } else {
                            self.operand_tag(&args[0])
                        };
                        after.push(Action::SetTag { tag_local, value });
                    } else if let Some(callee) = callee {
                        let (taken, unknown): (Vec<_>, Vec<_>) =
                            targets.into_iter().partition(|(index, _)| *index < MAX_RET_TAGS);
                        if !taken.is_empty() {
                            after.push(Action::TakeRets { callee, targets: taken });
                        }
                        let assignments: Vec<_> = unknown
                            .into_iter()
                            .map(|(_, tag)| (tag, TagValue::Const(UNKNOWN_TAG)))
                            .collect();
                        if !assignments.is_empty() {
                            after.push(Action::SetTags { assignments });
                        }
                    } else {
                        let assignments: Vec<_> = targets
                            .into_iter()
                            .map(|(_, tag)| (tag, TagValue::Const(UNKNOWN_TAG)))
                            .collect();
                        if !assignments.is_empty() {
                            after.push(Action::SetTags { assignments });
                        }
                    }
                    // A destination in memory gets the returned tags in shadow memory.
                    let dest_in_memory = self.is_memory(destination) && self.is_sized(dest_ty);
                    let mut ret_tags = vec![];
                    if dest_in_memory {
                        let span = body.blocks()[0].terminator.source_info.span;
                        let paths = self.flat_paths(dest_ty);
                        if is_pointer(dest_ty) && is_allocator {
                            ret_tags.push((vec![], TagValue::Const(ROOT_TAG)));
                        } else if is_pointer(dest_ty) && provenance_intrinsic(body, func) {
                            let tag = self.operand_tag(&args[0]);
                            ret_tags.push((vec![], self.read_tag_before(body, tag, &mut before)));
                        } else if let Some(callee) = callee {
                            let mut targets = vec![];
                            for (index, path) in paths.into_iter().enumerate().take(MAX_RET_TAGS) {
                                let tag_local = body.new_local(
                                    Ty::unsigned_ty(UintTy::U8),
                                    span,
                                    Mutability::Mut,
                                );
                                targets.push((index, tag_local));
                                ret_tags.push((path, TagValue::Local(tag_local)));
                            }
                            if !targets.is_empty() {
                                after.push(Action::TakeRets { callee, targets });
                            }
                        }
                    }
                    self.write(body, destination, &mut after);
                    if dest_in_memory {
                        self.store_tags(destination, dest_ty, ret_tags, &mut after);
                    }
                }
            }
            TerminatorKind::Drop { place, .. } => {
                // Dropping passes `&mut place` to the drop glue: a reborrow, which reads the
                // place, then a call. The glue's own accesses are checked through the new tag.
                self.read(body, place, &mut before);
                let ty = place.ty(body.locals()).unwrap();
                let drop_glue = Instance::resolve_drop_in_place(ty);
                // A local whose address is not otherwise taken is only reached through this
                // reference, a child of its allocation's root.
                let parent = self.place_tag(body, place).unwrap_or(TagValue::Const(ROOT_TAG));
                // The drop glue reads the pointers of a local with tag locals from memory.
                if !self.is_memory(place) && self.is_sized(ty) {
                    let tags: Vec<_> = self
                        .flat_paths(ty)
                        .into_iter()
                        .map(|suffix| {
                            let tag = self.place_ptr_tag(place, &suffix);
                            (suffix, tag)
                        })
                        .collect();
                    if !tags.is_empty() {
                        self.store_tags(place, ty, tags, &mut before);
                    }
                }
                before.push(Action::DropRetag {
                    place: place.clone(),
                    parent,
                    callee: instance_id(drop_glue),
                });
            }
            TerminatorKind::SwitchInt { discr: operand, .. }
            | TerminatorKind::Assert { cond: operand, .. } => {
                self.read_operand(body, operand, &mut before)
            }
            TerminatorKind::Return => {
                let tags: Vec<_> = self
                    .flat_paths(body.locals()[0].ty)
                    .into_iter()
                    .take(MAX_RET_TAGS)
                    .map(|path| self.place_ptr_tag(&Place::from(0), &path))
                    .collect();
                for tag_local in &self.protector_tags {
                    before.push(Action::EndProtector { tag_local: *tag_local });
                }
                if !tags.is_empty() || self.frame_count.is_some() {
                    before.push(Action::Return { tags });
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
            Action::Access { place, tag, is_write, guard } => {
                let ty = place.ty(body.locals()).unwrap();
                let model = if self.is_sized(ty) {
                    KaniModel::AliasingAccess
                } else {
                    KaniModel::AliasingAccessUnsized
                };
                let enabled = self.guard_operand(body, &guard, source, position);
                let ptr = self.address_of(body, place, source, position);
                let code = body.new_local(Ty::unsigned_ty(UintTy::U8), span, Mutability::Not);
                let access = self.model(model, vec![ty]);
                let args = vec![
                    enabled,
                    self.tag_operand(body, tag, source, position),
                    Operand::Move(Place::from(ptr)),
                    bool_operand(is_write, span),
                ];
                body.insert_call(&access, source, position, args, Place::from(code));
                self.insert_access_checks(body, code, is_write, source, position);
            }
            Action::AccessCount { ptr, tag, count, elem, is_write } => {
                let ptr = self.raw_ptr_operand(body, ptr, elem, source, position);
                let code = body.new_local(Ty::unsigned_ty(UintTy::U8), span, Mutability::Not);
                let access = self.model(KaniModel::AliasingAccessCount, vec![elem]);
                let args = vec![
                    self.tag_operand(body, tag, source, position),
                    ptr,
                    count,
                    bool_operand(is_write, span),
                ];
                body.insert_call(&access, source, position, args, Place::from(code));
                self.insert_access_checks(body, code, is_write, source, position);
            }
            Action::AccessBytes { place, offset, size, tag, is_write } => {
                let base = self.byte_address(body, place, source, position);
                let offset = body.new_uint_operand(offset as u128, UintTy::Usize, span);
                let ptr = body.insert_binary_op(BinOp::Offset, base, offset, source, position);
                let elem = Ty::unsigned_ty(UintTy::U8);
                let code = body.new_local(elem, span, Mutability::Not);
                let access = self.model(KaniModel::AliasingAccessCount, vec![elem]);
                let args = vec![
                    self.tag_operand(body, tag, source, position),
                    Operand::Move(Place::from(ptr)),
                    body.new_uint_operand(size as u128, UintTy::Usize, span),
                    bool_operand(is_write, span),
                ];
                body.insert_call(&access, source, position, args, Place::from(code));
                self.insert_access_checks(body, code, is_write, source, position);
            }
            Action::Expose { tag } => {
                let expose = self.model(KaniModel::AliasingExpose, vec![]);
                let args = vec![self.tag_operand(body, tag, source, position)];
                let ret = unit_place(body, span);
                body.insert_call(&expose, source, position, args, ret);
            }
            Action::Dealloc { ptr, tag, size } => {
                let ptr_ty = ptr.ty(body.locals()).unwrap();
                let u8_ptr = Ty::new_ptr(Ty::unsigned_ty(UintTy::U8), Mutability::Not);
                let ptr = if ptr_ty == u8_ptr {
                    ptr
                } else {
                    let cast = body.insert_ptr_cast(
                        ptr,
                        Ty::unsigned_ty(UintTy::U8),
                        Mutability::Not,
                        source,
                        position,
                    );
                    Operand::Move(Place::from(cast))
                };
                let code = body.new_local(Ty::unsigned_ty(UintTy::U8), span, Mutability::Not);
                let dealloc = self.model(KaniModel::AliasingDealloc, vec![]);
                let args = vec![self.tag_operand(body, tag, source, position), ptr, size];
                body.insert_call(&dealloc, source, position, args, Place::from(code));
                // Deallocating writes through the pointer.
                self.insert_access_checks(body, code, true, source, position);
                self.insert_ne_check(
                    body,
                    code,
                    ACCESS_PROTECTED_DEALLOC,
                    MSG_DEALLOC_PROTECTED,
                    source,
                    position,
                );
            }
            Action::ClearTags { place } => {
                let ty = place.ty(body.locals()).unwrap();
                let size = ty.layout().unwrap().shape().size.bytes();
                let slot = self.byte_address(body, place, source, position);
                let clear = self.model(KaniModel::AliasingClearTags, vec![]);
                let ret = unit_place(body, span);
                let args = vec![slot, body.new_uint_operand(size as u128, UintTy::Usize, span)];
                body.insert_call(&clear, source, position, args, ret);
            }
            Action::StoreTag { place, tag, guard, outlives_frame } => {
                let enabled = self.guard_operand(body, &guard, source, position);
                let tag = self.tag_operand(body, tag, source, position);
                let slot = self.byte_address(body, place, source, position);
                let store = self.model(KaniModel::AliasingStoreTag, vec![]);
                let ret = unit_place(body, span);
                let args = vec![enabled, slot, tag, bool_operand(outlives_frame, span)];
                body.insert_call(&store, source, position, args, ret);
            }
            Action::ForgetTags { ptr } => {
                let ptr =
                    self.raw_ptr_operand(body, ptr, Ty::unsigned_ty(UintTy::U8), source, position);
                let forget = self.model(KaniModel::AliasingForgetTags, vec![]);
                let ret = unit_place(body, span);
                body.insert_call(&forget, source, position, vec![ptr], ret);
            }
            Action::ForgetAll => {
                let forget = self.model(KaniModel::AliasingForgetAll, vec![]);
                let ret = unit_place(body, span);
                body.insert_call(&forget, source, position, vec![], ret);
            }
            Action::EndProtector { tag_local } => {
                let code = body.new_local(Ty::unsigned_ty(UintTy::U8), span, Mutability::Not);
                let end = self.model(KaniModel::AliasingEndProtector, vec![]);
                let args = vec![Operand::Copy(Place::from(tag_local))];
                body.insert_call(&end, source, position, args, Place::from(code));
                self.insert_access_checks(body, code, true, source, position);
            }
            Action::Unsupported { msg } => {
                body.insert_check(&self.pass.unsupported_check_type, source, position, None, &msg);
            }
            Action::SetTag { tag_local, value } => {
                let operand = self.tag_operand(body, value, source, position);
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
                        let operand = self.tag_operand(body, value.clone(), source, position);
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
            Action::NewBorrow {
                tag_local,
                place,
                parent,
                cell_mask,
                is_shared,
                is_protected,
                is_strong,
                guard,
            } => {
                let ty = place.ty(body.locals()).unwrap();
                let model = if self.is_sized(ty) {
                    KaniModel::AliasingNewBorrow
                } else {
                    KaniModel::AliasingNewBorrowUnsized
                };
                let enabled = self.guard_operand(body, &guard, source, position);
                let ptr = self.address_of(body, place, source, position);
                let new_borrow = self.model(model, vec![ty]);
                let mut args = vec![
                    enabled,
                    self.tag_operand(body, parent, source, position),
                    Operand::Move(Place::from(ptr)),
                ];
                if model == KaniModel::AliasingNewBorrow {
                    args.push(body.new_uint_operand(cell_mask as u128, UintTy::U64, span));
                }
                args.push(bool_operand(self.is_freeze(ty), span));
                args.push(bool_operand(is_shared, span));
                args.push(bool_operand(is_protected, span));
                args.push(bool_operand(is_strong, span));
                body.insert_call(&new_borrow, source, position, args, Place::from(tag_local));
            }
            Action::ReadOutsideCells { place, tag, cell_mask, guard } => {
                let ty = place.ty(body.locals()).unwrap();
                let enabled = self.guard_operand(body, &guard, source, position);
                let ptr = self.address_of(body, place, source, position);
                let code = body.new_local(Ty::unsigned_ty(UintTy::U8), span, Mutability::Not);
                let read = self.model(KaniModel::AliasingReadOutsideCells, vec![ty]);
                let args = vec![
                    enabled,
                    self.tag_operand(body, tag, source, position),
                    Operand::Move(Place::from(ptr)),
                    body.new_uint_operand(cell_mask as u128, UintTy::U64, span),
                ];
                body.insert_call(&read, source, position, args, Place::from(code));
                self.insert_access_checks(body, code, false, source, position);
            }
            Action::DropRetag { place, parent, callee } => {
                let tag_local = body.new_local(Ty::unsigned_ty(UintTy::U8), span, Mutability::Not);
                self.insert(
                    body,
                    Action::NewBorrow {
                        tag_local,
                        place,
                        parent,
                        cell_mask: 0,
                        is_shared: false,
                        is_protected: false,
                        is_strong: true,
                        guard: vec![],
                    },
                    source,
                    position,
                );
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
                    let tag = tags.get(index).cloned().unwrap_or(TagValue::Const(UNKNOWN_TAG));
                    args.push(self.tag_operand(body, tag, source, position));
                }
                let ret = unit_place(body, span);
                body.insert_call(&push, source, position, args, ret);
            }
            Action::Return { tags } => {
                let ret_model = self.model(KaniModel::AliasingReturn, vec![]);
                // Without a frame count, the function created no tags: passing the unknown tag
                // as the count keeps them all.
                let frame_count = match self.frame_count {
                    Some(local) => Operand::Copy(Place::from(local)),
                    None => body.new_uint_operand(UNKNOWN_TAG as u128, UintTy::U8, span),
                };
                let mut args = vec![
                    body.new_uint_operand(self.own_id as u128, UintTy::U64, span),
                    frame_count,
                ];
                for index in 0..MAX_RET_TAGS {
                    let tag = tags.get(index).cloned().unwrap_or(TagValue::Const(UNKNOWN_TAG));
                    args.push(self.tag_operand(body, tag, source, position));
                }
                let ret = unit_place(body, span);
                body.insert_call(&ret_model, source, position, args, ret);
            }
            Action::TakeRets { callee, targets } => {
                for (index, tag_local) in targets {
                    let ret_tag = self.model(KaniModel::AliasingRetTag, vec![]);
                    let args = vec![
                        body.new_uint_operand(callee as u128, UintTy::U64, span),
                        body.new_uint_operand(index as u128, UintTy::Usize, span),
                    ];
                    body.insert_call(&ret_tag, source, position, args, Place::from(tag_local));
                }
                let end_ret = self.model(KaniModel::AliasingEndRet, vec![]);
                let ret = unit_place(body, span);
                body.insert_call(&end_ret, source, position, vec![], ret);
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
        self.insert_ne_check(body, code, ACCESS_NOT_EXPOSED, MSG_NOT_EXPOSED, source, position);
        // A read can break a protector too: it disables a protected Active reference.
        self.insert_ne_check(body, code, ACCESS_PROTECTOR, MSG_PROTECTOR, source, position);
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
        let span = source.span(body.blocks());
        for (unknown, msg) in UNKNOWN_RESULTS {
            let unknown = body.new_uint_operand(unknown as u128, UintTy::U8, span);
            let decided = body.insert_binary_op(
                BinOp::Ne,
                Operand::Copy(Place::from(code)),
                unknown,
                source,
                position,
            );
            body.insert_check(&self.pass.unknown_check_type, source, position, Some(decided), msg);
        }
    }

    /// A `bool` operand that is true if every place of `guard` has its variant.
    fn guard_operand(
        &self,
        body: &mut MutableBody,
        guard: &Guard,
        source: &mut SourceInstruction,
        position: InsertPosition,
    ) -> Operand {
        let span = source.span(body.blocks());
        let mut enabled: Option<Local> = None;
        for (place, discr) in guard {
            let value =
                body.insert_assignment(Rvalue::Discriminant(place.clone()), source, position);
            let value = body.insert_assignment(
                Rvalue::Cast(
                    CastKind::IntToInt,
                    Operand::Copy(Place::from(value)),
                    Ty::unsigned_ty(UintTy::U64),
                ),
                source,
                position,
            );
            let expected = body.new_uint_operand(*discr as u64 as u128, UintTy::U64, span);
            let is_variant = body.insert_binary_op(
                BinOp::Eq,
                Operand::Copy(Place::from(value)),
                expected,
                source,
                position,
            );
            enabled = Some(match enabled {
                None => is_variant,
                Some(previous) => body.insert_binary_op(
                    BinOp::BitAnd,
                    Operand::Copy(Place::from(previous)),
                    Operand::Copy(Place::from(is_variant)),
                    source,
                    position,
                ),
            });
        }
        enabled.map_or_else(|| bool_operand(true, span), |local| Operand::Copy(Place::from(local)))
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

    fn tag_operand(
        &self,
        body: &mut MutableBody,
        tag: TagValue,
        source: &mut SourceInstruction,
        position: InsertPosition,
    ) -> Operand {
        let span = source.span(body.blocks());
        match tag {
            TagValue::Const(value) => body.new_uint_operand(value as u128, UintTy::U8, span),
            TagValue::Local(local) => Operand::Copy(Place::from(local)),
            TagValue::Load(place) => {
                let slot = self.byte_address(body, place, source, position);
                let tag = body.new_local(Ty::unsigned_ty(UintTy::U8), span, Mutability::Not);
                let load = self.model(KaniModel::AliasingLoadTag, vec![]);
                let args = vec![slot];
                body.insert_call(&load, source, position, args, Place::from(tag));
                Operand::Copy(Place::from(tag))
            }
        }
    }

    /// A local holding `&raw const place`. The address of `*p`, for a reference or raw pointer
    /// `p`, is `p` itself: computing it without a dereference avoids the validity checks that a
    /// dereference gets, which fail for pointers in inactive enum variants that guarded actions
    /// skip.
    fn address_of(
        &self,
        body: &mut MutableBody,
        place: Place,
        source: &mut SourceInstruction,
        position: InsertPosition,
    ) -> Local {
        if let Some((ProjectionElem::Deref, prefix)) = place.projection.split_last() {
            let pointer = Place { local: place.local, projection: prefix.to_vec() };
            let pointer_ty = pointer.ty(body.locals()).unwrap();
            if is_pointer(pointer_ty) {
                let pointee = pointer_ty.kind().builtin_deref(true).unwrap().ty;
                return body.insert_assignment(
                    Rvalue::Cast(
                        CastKind::Transmute,
                        Operand::Copy(pointer),
                        Ty::new_ptr(pointee, Mutability::Not),
                    ),
                    source,
                    position,
                );
            }
        }
        body.insert_assignment(Rvalue::AddressOf(RawPtrKind::Const, place), source, position)
    }

    /// A `*const u8` with the address of `place`.
    fn byte_address(
        &self,
        body: &mut MutableBody,
        place: Place,
        source: &mut SourceInstruction,
        position: InsertPosition,
    ) -> Operand {
        let ptr =
            body.insert_assignment(Rvalue::AddressOf(RawPtrKind::Const, place), source, position);
        let cast = body.insert_ptr_cast(
            Operand::Move(Place::from(ptr)),
            Ty::unsigned_ty(UintTy::U8),
            Mutability::Not,
            source,
            position,
        );
        Operand::Move(Place::from(cast))
    }

    /// A raw pointer to `elem` with the address of the pointer or reference `ptr`.
    fn raw_ptr_operand(
        &self,
        body: &mut MutableBody,
        ptr: Operand,
        elem: Ty,
        source: &mut SourceInstruction,
        position: InsertPosition,
    ) -> Operand {
        let ptr_ty = ptr.ty(body.locals()).unwrap();
        if ptr_ty == Ty::new_ptr(elem, Mutability::Not) {
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
            let raw_ty =
                Ty::new_ptr(ptr_ty.kind().builtin_deref(true).unwrap().ty, Mutability::Not);
            if raw_ty == Ty::new_ptr(elem, Mutability::Not) {
                Operand::Move(Place::from(raw))
            } else {
                let cast = body.insert_ptr_cast(
                    Operand::Move(Place::from(raw)),
                    elem,
                    Mutability::Not,
                    source,
                    position,
                );
                Operand::Move(Place::from(cast))
            }
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

    fn is_unpin(&self, ty: Ty) -> bool {
        let internal = rustc_internal::internal(self.tcx, ty);
        let typing_env = TypingEnv::fully_monomorphized();
        internal.is_unpin(self.tcx, typing_env) && internal.is_unsafe_unpin(self.tcx, typing_env)
    }

    fn is_freeze(&self, ty: Ty) -> bool {
        rustc_internal::internal(self.tcx, ty).is_freeze(self.tcx, TypingEnv::fully_monomorphized())
    }
}

/// The offset and size of the tag of an enum of type `ty`, and its untagged variant if a niche
/// encodes the tag; `None` if values of `ty` store no tag.
fn enum_tag_bytes(ty: Ty) -> Option<(u64, u64, Option<rustc_public::ty::VariantIdx>)> {
    let shape = ty.layout().ok()?.shape();
    let VariantsShape::Multiple { tag, tag_encoding, tag_field, .. } = &shape.variants else {
        return None;
    };
    let FieldsShape::Arbitrary { offsets } = &shape.fields else { return None };
    let offset = offsets.get(*tag_field)?.bytes() as u64;
    let primitive = match tag {
        Scalar::Initialized { value, .. } | Scalar::Union { value } => *value,
    };
    let size = primitive.size(&MachineInfo::target()).bytes() as u64;
    let untagged = match tag_encoding {
        TagEncoding::Direct => None,
        TagEncoding::Niche { untagged_variant, .. } => Some(*untagged_variant),
    };
    Some((offset, size, untagged))
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

/// Whether `instance` belongs to the module that `kani_core::kani_aliasing!` generates in the Kani
/// library (`kani::aliasing`), or in `core` when verifying the standard library.
fn is_aliasing_model(instance: Instance) -> bool {
    let name = instance.name();
    name.starts_with("kani::aliasing::") || name.contains("::kani::aliasing::")
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
