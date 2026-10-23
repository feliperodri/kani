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
//! Pointers whose provenance this pass does not follow get the *wildcard* tag, which the library
//! neither checks nor updates. This includes pointers read from memory (other than through a
//! `Box`), pointers returned by indirect calls, places with several dereferences, and integer to
//! pointer casts. Missing these accesses means missing some undefined behavior, never reporting
//! undefined behavior that is not there.
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
use rustc_middle::ty::{TyCtxt, TypingEnv};
use rustc_public::mir::mono::{Instance, InstanceKind};
use rustc_public::mir::{
    AggregateKind, BinOp, Body, BorrowKind, CastKind, ConstOperand, Local, Mutability, Operand,
    Place, PointerCoercion, ProjectionElem, RawPtrKind, Rvalue, StatementKind, TerminatorKind,
};
use rustc_public::rustc_internal;
use rustc_public::ty::{FnDef, GenericArgKind, GenericArgs, MirConst, RigidTy, Span, Ty, UintTy};
use std::collections::hash_map::DefaultHasher;
use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};
use tracing::trace;

/// Tag values shared with `kani_core::kani_aliasing`.
const ROOT_TAG: u8 = 0;
const WILDCARD_TAG: u8 = u8::MAX;
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
    /// Set a tag local.
    SetTag { tag_local: Local, value: TagValue },
    /// Create a reference through a pointer tagged `parent`.
    NewBorrow { tag_local: Local, parent: TagValue, is_shared: bool },
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
    /// The ghost tag local of every local of reference or raw pointer type.
    tags: HashMap<Local, Local>,
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
        let pointer_locals: Vec<Local> = body
            .locals()
            .iter()
            .enumerate()
            .filter(|(_, decl)| is_pointer(decl.ty))
            .map(|(local, _)| local)
            .collect();
        for local in pointer_locals {
            let tag_local = body.new_local(Ty::unsigned_ty(UintTy::U8), span, Mutability::Mut);
            self.tags.insert(local, tag_local);
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
            let Some(&tag_local) = self.tags.get(&local) else { continue };
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
        let mut locals: Vec<(Local, Local)> =
            self.tags.iter().map(|(local, tag)| (*local, *tag)).collect();
        locals.sort();
        for (local, tag_local) in locals {
            if local == 0 || local > body.arg_count() {
                self.insert(
                    body,
                    Action::SetTag { tag_local, value: TagValue::Const(WILDCARD_TAG) },
                    &mut source,
                    InsertPosition::Before,
                );
            }
        }
    }

    /// The tag to use for an access to `place`, if the access is checked: the tag of the pointer
    /// it goes through, or the root tag for a local whose address is taken.
    fn place_tag(&self, body: &MutableBody, place: &Place) -> Option<TagValue> {
        let derefs = place.projection.iter().filter(|e| matches!(e, ProjectionElem::Deref)).count();
        match (derefs, place.projection.first()) {
            (0, _) => {
                self.address_taken.contains(&place.local).then_some(TagValue::Const(ROOT_TAG))
            }
            (1, Some(ProjectionElem::Deref)) => {
                let ty = body.locals()[place.local].ty;
                if ty.kind().is_box() {
                    Some(TagValue::Const(ROOT_TAG))
                } else {
                    self.tags.get(&place.local).map(|tag| TagValue::Local(*tag))
                }
            }
            _ => None,
        }
    }

    /// The tag of the pointer an operand evaluates to.
    fn operand_tag(&self, operand: &Operand) -> TagValue {
        match operand {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => self
                .tags
                .get(&place.local)
                .map_or(TagValue::Const(WILDCARD_TAG), |tag| TagValue::Local(*tag)),
            _ => TagValue::Const(WILDCARD_TAG),
        }
    }

    /// The tag local of `place`, if it is a whole local of pointer type.
    fn dest_tag(&self, place: &Place) -> Option<Local> {
        if place.projection.is_empty() { self.tags.get(&place.local).copied() } else { None }
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

    fn statement_actions(&self, body: &MutableBody, kind: &StatementKind) -> Vec<Action> {
        let mut actions = vec![];
        match kind {
            StatementKind::Assign(lhs, rvalue) => {
                let dest = self.dest_tag(lhs);
                let mut new_tag = None;
                match rvalue {
                    Rvalue::Ref(_, borrow_kind, place) => {
                        let parent =
                            self.place_tag(body, place).unwrap_or(TagValue::Const(WILDCARD_TAG));
                        let ty = place.ty(body.locals()).unwrap();
                        let tracked =
                            !matches!(borrow_kind, BorrowKind::Fake(_)) && self.is_freeze(ty);
                        if tracked {
                            // Creating a reference reads the referenced memory. The read of an
                            // unsized place is not checked (`Access` skips it).
                            self.read(body, place, &mut actions);
                            if let Some(tag_local) = dest {
                                actions.push(Action::NewBorrow {
                                    tag_local,
                                    parent,
                                    is_shared: matches!(borrow_kind, BorrowKind::Shared),
                                });
                            }
                        } else {
                            new_tag = Some(parent);
                        }
                    }
                    Rvalue::AddressOf(_, place) => {
                        new_tag = Some(
                            self.place_tag(body, place).unwrap_or(TagValue::Const(WILDCARD_TAG)),
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
                            _ => TagValue::Const(WILDCARD_TAG),
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
                    let value = new_tag.unwrap_or(TagValue::Const(WILDCARD_TAG));
                    actions.push(Action::SetTag { tag_local, value });
                }
            }
            StatementKind::SetDiscriminant { place, .. } => self.write(body, place, &mut actions),
            StatementKind::FakeRead(..)
            | StatementKind::StorageLive(_)
            | StatementKind::StorageDead(_)
            | StatementKind::PlaceMention(_)
            | StatementKind::AscribeUserType { .. }
            | StatementKind::Coverage(_)
            | StatementKind::Intrinsic(_)
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
                                Action::SetTag { tag_local, value: TagValue::Const(WILDCARD_TAG) }
                            }
                        });
                    }
                    self.write(body, destination, &mut after);
                }
            }
            TerminatorKind::Drop { place, .. } => self.write(body, place, &mut before),
            TerminatorKind::SwitchInt { discr: operand, .. }
            | TerminatorKind::Assert { cond: operand, .. } => {
                self.read_operand(body, operand, &mut before)
            }
            TerminatorKind::Return => {
                let tag = self.tags.get(&0).map(|tag| TagValue::Local(*tag));
                if tag.is_some() || self.frame_count.is_some() {
                    let tag = tag.unwrap_or(TagValue::Const(WILDCARD_TAG));
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
                if !self.is_sized(ty) {
                    return;
                }
                let ptr = body.insert_assignment(
                    Rvalue::AddressOf(RawPtrKind::Const, place),
                    source,
                    position,
                );
                let code = body.new_local(Ty::unsigned_ty(UintTy::U8), span, Mutability::Not);
                let access = self.model(KaniModel::AliasingAccess, vec![ty]);
                let args = vec![
                    self.tag_operand(body, tag, span),
                    Operand::Move(Place::from(ptr)),
                    bool_operand(is_write, span),
                ];
                body.insert_call(&access, source, position, args, Place::from(code));
                self.insert_ne_check(
                    body,
                    code,
                    ACCESS_INVALIDATED,
                    MSG_INVALIDATED,
                    source,
                    position,
                );
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
            Action::SetTag { tag_local, value } => {
                let operand = self.tag_operand(body, value, span);
                body.assign_to(
                    Place::from(tag_local),
                    Rvalue::Use(operand, rustc_public::mir::WithRetag::No),
                    source,
                    position,
                );
            }
            Action::NewBorrow { tag_local, parent, is_shared } => {
                let new_borrow = self.model(KaniModel::AliasingNewBorrow, vec![]);
                let args =
                    vec![self.tag_operand(body, parent, span), bool_operand(is_shared, span)];
                body.insert_call(&new_borrow, source, position, args, Place::from(tag_local));
            }
            Action::PushCall { callee, tags } => {
                let push = self.model(KaniModel::AliasingPushCall, vec![]);
                let mut args = vec![body.new_uint_operand(callee as u128, UintTy::U64, span)];
                for index in 0..MAX_ARG_TAGS {
                    let tag = tags.get(index).copied().unwrap_or(TagValue::Const(WILDCARD_TAG));
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
                    None => body.new_uint_operand(WILDCARD_TAG as u128, UintTy::U8, span),
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
