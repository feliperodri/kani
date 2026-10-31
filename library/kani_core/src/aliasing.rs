// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Runtime model of the aliasing checks (`-Z aliasing-checks`).
//!
//! The rules are Tree Borrows' rules at one memory location, restricted to what the
//! documentation lists; their transition core is `kani_aliasing_monitor!`
//! (`aliasing_monitor.rs`), which is verified with Verus. This module holds the global state,
//! turns pointers into the facts the monitor needs (does an access cover the tracked byte, is
//! that byte inside an `UnsafeCell`), passes tags across calls, and reports what the checks
//! cannot decide as unsupported.
//!
//! Like the memory-initialization checks, the state is tracked for a single byte of memory,
//! chosen non-deterministically for each harness: if some byte is accessed in a way the rules
//! reject, there is a choice that tracks that byte. The compiler inserts calls to the functions
//! below; see `kani_middle::transform::check_aliasing`. It does not instrument any function of
//! this module.

// Definitions in this module are not meant to be visible to the end user, only the compiler.
#![allow(dead_code)]

#[macro_export]
#[allow(clippy::crate_in_macro_def)]
macro_rules! kani_aliasing {
    ($core:tt) => {
        use $core::marker::MetaSized;

        kani_core::kani_aliasing_monitor!();

        /// Number of pointers in the arguments, and in the returned value, of a direct call
        /// whose tags are passed between caller and callee.
        const MAX_ARG_TAGS: usize = 8;
        const MAX_RET_TAGS: usize = 4;

        // The functions below that are not generic are exported as `__VERIFIER_kani_aliasing_*`,
        // like the monitor's (see `kani_aliasing_monitor!`): CBMC's contract instrumentation does
        // not instrument them, so a function contract's `modifies` check is not threaded through
        // the instrumentation of every access. They only write the two statics below.

        /// The monitor's state for the tracked byte.
        // Contracts' `modifies` checks must let the instrumentation write this state; the
        // compiler finds it by this marker.
        #[kanitool::fn_marker = "KaniAliasingState"]
        static mut ALIASING_STATE: MonitorState = monitor_new();

        /// Tags passed across calls. A caller records the tags of the pointers in the arguments
        /// of a direct call, keyed by the callee; the callee records the tags in the value it
        /// returns, keyed by itself.
        struct CallState {
            call_callee: u64,
            call_tags: [u8; MAX_ARG_TAGS],
            ret_callee: u64,
            /// The trait method the function that returned implements, for calls through `dyn`.
            ret_method: u64,
            ret_tags: [u8; MAX_RET_TAGS],
            /// Incremented when memory may have been written without instrumentation: it is
            /// part of every object's epoch.
            generation: u8,
        }

        #[kanitool::fn_marker = "KaniAliasingCallState"]
        static mut CALL_STATE: CallState = CallState {
            call_callee: 0,
            call_tags: [UNKNOWN_TAG; MAX_ARG_TAGS],
            ret_callee: 0,
            ret_method: 0,
            ret_tags: [UNKNOWN_TAG; MAX_RET_TAGS],
            generation: 0,
        };

        #[unsafe(export_name = "__VERIFIER_kani_aliasing_state")]
        fn state() -> &'static mut MonitorState {
            unsafe { &mut *(&raw mut ALIASING_STATE) }
        }

        #[unsafe(export_name = "__VERIFIER_kani_aliasing_calls")]
        fn calls() -> &'static mut CallState {
            unsafe { &mut *(&raw mut CALL_STATE) }
        }

        /// Choose the tracked byte.
        #[kanitool::disable_checks(pointer)]
        #[kanitool::fn_marker = "AliasingInitializeModel"]
        #[unsafe(export_name = "__VERIFIER_kani_aliasing_aliasing_initialize")]
        fn aliasing_initialize() {
            shadow_decl();
            monitor_initialize(state(), super::any(), super::any());
            calls().call_callee = 0;
            calls().ret_callee = 0;
            calls().generation = 0;
        }

        /// Access `size` bytes at offset `offset` of object `obj` through `tag`. Return
        /// `ACCESS_OK` or the rule the access breaks.
        #[kanitool::disable_checks(pointer)]
        #[kanitool::fn_marker = "AliasingAccessBytesModel"]
        #[unsafe(export_name = "__VERIFIER_kani_aliasing_aliasing_access_bytes")]
        fn aliasing_access_bytes(
            tag: u8,
            obj: usize,
            offset: usize,
            size: usize,
            is_write: bool,
        ) -> u8 {
            let s = state();
            if !monitor_covers(s, obj, offset, size) {
                return ACCESS_OK;
            }
            let code = if tag == EXPOSED_TAG {
                monitor_wildcard_access(s, is_write)
            } else if tag < s.count {
                monitor_access(s, tag, is_write)
            } else {
                ACCESS_UNKNOWN_TAG
            };
            code
        }

        // Tags of pointers stored in memory live in CBMC's shadow memory, through the hooks
        // below, which the compiler lowers to `__CPROVER_field_decl_*`, `__CPROVER_set_field`
        // (on every byte of a word) and `__CPROVER_get_field` (the maximum over its bytes).
        // Fields are 8 bits per byte. A store records, on every byte of the pointer's first word,
        // its tag plus one and the epoch of the object that holds it, each with its complement,
        // so that a load sees whether all bytes hold the same ones (the maximum of a value and
        // the maximum of its complement only agree then). Every other write to memory sets the
        // tag's complement to all ones on the words it overlaps, which no load accepts. Copy
        // intrinsics, and writes of large values, bump the epoch of the object they write, kept
        // on its first word. A load accepts the tag only if all of this checks out; otherwise the
        // tag is unknown.
        //
        // This relies on every write to memory being instrumented. Loop contracts (whose
        // assigns CBMC havocs) and C functions write memory without instrumentation: the
        // compiler calls `aliasing_forget_all` where they may, which increments a generation
        // that is part of every object's epoch.
        //
        // The models have `__VERIFIER` names so that CBMC's contract instrumentation leaves the
        // shadow-memory built-ins in them alone.

        const FIELD_TAG: u8 = 0;
        const FIELD_TAG_INV: u8 = 1;
        const FIELD_EPOCH_AT: u8 = 2;
        const FIELD_EPOCH_AT_INV: u8 = 3;
        const FIELD_EPOCH: u8 = 4;

        /// Words of memory: the shadow memory of a pointer is that of its first word.
        type Word = *const *const u8;
        const WORD: usize = size_of::<Word>();

        /// Writes of values larger than this many words bump the epoch of the object instead
        /// (`aliasing_clear_tags` clears at most this many words plus one).
        const MAX_CLEARED_WORDS: usize = 8;

        #[kanitool::fn_marker = "AliasingShadowDeclHook"]
        #[inline(never)]
        fn shadow_decl() {}

        /// Set shadow-memory field `field` (a constant) of every byte of the word at `ptr` to
        /// `value`, if the word is inside its object (of the first word of the object for
        /// `FIELD_EPOCH`).
        #[kanitool::fn_marker = "AliasingShadowSetHook"]
        #[inline(never)]
        fn shadow_set(_ptr: *const Word, _field: u8, _value: u8) {}

        /// The maximum of shadow-memory field `field` (a constant) over the bytes of the word at
        /// `ptr`, or 0 if the word is not inside its object.
        #[kanitool::fn_marker = "AliasingShadowGetHook"]
        #[inline(never)]
        fn shadow_get(_ptr: *const Word, _field: u8) -> u8 {
            0
        }

        /// The last epoch: an object that reaches it keeps no tags.
        const SATURATED_EPOCH: u8 = u8::MAX;

        /// The epoch of the object that holds `slot`: its own epoch plus the generation. Both
        /// only increase, so the sum changes whenever either does, until it saturates.
        #[unsafe(export_name = "__VERIFIER_kani_aliasing_epoch_of")]
        fn epoch_of(slot: *const Word) -> u8 {
            let epoch = shadow_get(slot, FIELD_EPOCH) as u16 + calls().generation as u16;
            if epoch >= SATURATED_EPOCH as u16 { SATURATED_EPOCH } else { epoch as u8 }
        }

        /// Memory may have been written without instrumentation: forget every stored tag.
        #[kanitool::fn_marker = "AliasingForgetAllModel"]
        #[unsafe(export_name = "__VERIFIER_kani_aliasing_aliasing_forget_all")]
        fn aliasing_forget_all() {
            let generation = calls().generation;
            if generation < SATURATED_EPOCH {
                calls().generation = generation + 1;
            }
        }

        /// Forget the tags stored in the words that the `size` bytes at `slot`, just written,
        /// overlap.
        #[kanitool::fn_marker = "AliasingClearTagsModel"]
        #[unsafe(export_name = "__VERIFIER_kani_aliasing_aliasing_clear_tags")]
        fn aliasing_clear_tags(slot: *const u8, size: usize) {
            if size == 0 {
                return;
            }
            if size > MAX_CLEARED_WORDS * WORD {
                aliasing_forget_tags(slot);
                return;
            }
            // Written out rather than a loop: the offset may be symbolic, and a loop here would
            // be subject to the harness's unwinding bound.
            let in_word = super::mem::pointer_offset(slot) % WORD;
            let first = slot.wrapping_sub(in_word);
            let end = in_word.wrapping_add(size);
            clear_word(first, 0, end);
            clear_word(first, 1, end);
            clear_word(first, 2, end);
            clear_word(first, 3, end);
            clear_word(first, 4, end);
            clear_word(first, 5, end);
            clear_word(first, 6, end);
            clear_word(first, 7, end);
            clear_word(first, 8, end);
        }

        /// Forget the tag in word `index` from `first`, if it starts before `end` bytes from
        /// `first`.
        #[unsafe(export_name = "__VERIFIER_kani_aliasing_clear_word")]
        fn clear_word(first: *const u8, index: usize, end: usize) {
            if index * WORD < end {
                shadow_set(first.wrapping_add(index * WORD) as *const Word, FIELD_TAG_INV, u8::MAX);
            }
        }

        /// Record `tag` as the tag of the pointer just stored at `slot`, if `enabled` (the
        /// pointer is in the active variant of its enums). If the memory may outlive the current
        /// function (`outlives_frame`), the tag outlives it too; a local of the function dies
        /// with it, and every load from it before then happens while its tags are alive.
        #[kanitool::fn_marker = "AliasingStoreTagModel"]
        #[unsafe(export_name = "__VERIFIER_kani_aliasing_aliasing_store_tag")]
        fn aliasing_store_tag(enabled: bool, slot: *const u8, tag: u8, outlives_frame: bool) {
            if !enabled {
                return;
            }
            let slot = slot as *const Word;
            let epoch = epoch_of(slot);
            if tag == UNKNOWN_TAG || epoch == SATURATED_EPOCH {
                shadow_set(slot, FIELD_TAG_INV, u8::MAX);
                return;
            }
            let stored = tag.wrapping_add(1);
            shadow_set(slot, FIELD_TAG, stored);
            shadow_set(slot, FIELD_TAG_INV, !stored);
            shadow_set(slot, FIELD_EPOCH_AT, epoch);
            shadow_set(slot, FIELD_EPOCH_AT_INV, !epoch);
            if outlives_frame {
                monitor_store(state(), tag);
            }
        }

        /// The tag of the pointer stored at `slot`.
        #[kanitool::fn_marker = "AliasingLoadTagModel"]
        #[unsafe(export_name = "__VERIFIER_kani_aliasing_aliasing_load_tag")]
        fn aliasing_load_tag(slot: *const u8) -> u8 {
            let slot = slot as *const Word;
            let stored = shadow_get(slot, FIELD_TAG);
            if stored == 0 || stored != !shadow_get(slot, FIELD_TAG_INV) {
                return UNKNOWN_TAG;
            }
            let epoch = shadow_get(slot, FIELD_EPOCH_AT);
            if epoch != !shadow_get(slot, FIELD_EPOCH_AT_INV) || epoch != epoch_of(slot) {
                return UNKNOWN_TAG;
            }
            stored.wrapping_sub(1)
        }

        /// The bytes of the object `ptr` points into were written without their tags (by a copy
        /// intrinsic, or a write of a large value): forget the tags stored in it.
        #[kanitool::fn_marker = "AliasingForgetTagsModel"]
        #[unsafe(export_name = "__VERIFIER_kani_aliasing_aliasing_forget_tags")]
        fn aliasing_forget_tags(ptr: *const u8) {
            let epoch = shadow_get(ptr as *const Word, FIELD_EPOCH);
            if epoch < SATURATED_EPOCH {
                shadow_set(ptr as *const Word, FIELD_EPOCH, epoch.wrapping_add(1));
            }
        }

        /// Access the `size_of::<T>()` bytes at `ptr` through `tag`.
        #[kanitool::disable_checks(pointer)]
        #[kanitool::fn_marker = "AliasingAccessModel"]
        fn aliasing_access<T>(enabled: bool, tag: u8, ptr: *const T, is_write: bool) -> u8 {
            if !enabled {
                return ACCESS_OK;
            }
            let obj = super::mem::pointer_object(ptr);
            let offset = super::mem::pointer_offset(ptr);
            aliasing_access_bytes(tag, obj, offset, size_of::<T>(), is_write)
        }

        /// Read the `size_of::<T>()` bytes at `ptr` through `tag`, except the bytes in
        /// `cell_mask` (bit `i` is byte `i`): the read that creating a shared reference to a type
        /// with an `UnsafeCell` performs, which does not touch the cell's bytes.
        #[kanitool::disable_checks(pointer)]
        #[kanitool::fn_marker = "AliasingReadOutsideCellsModel"]
        fn aliasing_read_outside_cells<T>(
            enabled: bool,
            tag: u8,
            ptr: *const T,
            cell_mask: u64,
        ) -> u8 {
            if !enabled {
                return ACCESS_OK;
            }
            let obj = super::mem::pointer_object(ptr);
            let offset = super::mem::pointer_offset(ptr);
            if in_cell(state(), obj, offset, size_of::<T>(), cell_mask) {
                return ACCESS_OK;
            }
            aliasing_access_bytes(tag, obj, offset, size_of::<T>(), false)
        }

        /// Access the `size_of_val(ptr)` bytes at `ptr` through `tag`, for an unsized `T`.
        #[kanitool::disable_checks(pointer)]
        #[kanitool::fn_marker = "AliasingAccessUnsizedModel"]
        fn aliasing_access_unsized<T: MetaSized>(
            enabled: bool,
            tag: u8,
            ptr: *const T,
            is_write: bool,
        ) -> u8 {
            if !enabled {
                return ACCESS_OK;
            }
            let size = match super::mem::checked_size_of_raw(ptr) {
                Some(size) => size,
                None => 0,
            };
            let thin = ptr as *const u8;
            let obj = super::mem::pointer_object(thin);
            let offset = super::mem::pointer_offset(thin);
            aliasing_access_bytes(tag, obj, offset, size, is_write)
        }

        /// Access `count` values of type `T` at `ptr` through `tag`, as memory intrinsics such as
        /// `copy_nonoverlapping` do.
        #[kanitool::disable_checks(pointer)]
        #[kanitool::fn_marker = "AliasingAccessCountModel"]
        fn aliasing_access_count<T>(tag: u8, ptr: *const T, count: usize, is_write: bool) -> u8 {
            let obj = super::mem::pointer_object(ptr);
            let offset = super::mem::pointer_offset(ptr);
            let size = count.saturating_mul(size_of::<T>());
            aliasing_access_bytes(tag, obj, offset, size, is_write)
        }

        /// Whether the tracked byte is in the `size` bytes at `offset` of `obj` and inside an
        /// `UnsafeCell` of the referent: bit `i` of `cell_mask` is byte `i` of the referent.
        #[unsafe(export_name = "__VERIFIER_kani_aliasing_in_cell")]
        fn in_cell(
            s: &MonitorState,
            obj: usize,
            offset: usize,
            size: usize,
            cell_mask: u64,
        ) -> bool {
            // `cell_mask` is a constant: without cells the answer does not depend on the tracked
            // byte, which keeps the monitor's cell bits concrete for symbolic execution.
            cell_mask != 0 && monitor_covers(s, obj, offset, size) && {
                let index = s.tracked_offset - offset;
                index < 64 && (cell_mask >> index) & 1 != 0
            }
        }

        /// Create a reference to `size` bytes at offset `offset` of object `obj` from a pointer
        /// tagged `parent`, and return its tag. A protected reference is the retag of a reference
        /// argument when a function starts; it stays protected until the function returns.
        ///
        /// The read access that creating a reference performs is checked separately, before.
        #[kanitool::disable_checks(pointer)]
        #[kanitool::fn_marker = "AliasingNewBorrowBytesModel"]
        #[allow(clippy::too_many_arguments)]
        #[unsafe(export_name = "__VERIFIER_kani_aliasing_aliasing_new_borrow_bytes")]
        fn aliasing_new_borrow_bytes(
            parent: u8,
            obj: usize,
            offset: usize,
            size: usize,
            cell_mask: u64,
            freeze: bool,
            is_shared: bool,
            is_protected: bool,
            is_strong: bool,
        ) -> u8 {
            let s = state();
            let covers = monitor_covers(s, obj, offset, size);
            let cell = in_cell(s, obj, offset, size, cell_mask);
            monitor_new_borrow(s, parent, covers, cell, freeze, is_shared, is_protected, is_strong)
        }

        /// `aliasing_new_borrow_bytes` for a reference to the `size_of::<T>()` bytes at `ptr`.
        #[kanitool::disable_checks(pointer)]
        #[kanitool::fn_marker = "AliasingNewBorrowModel"]
        #[allow(clippy::too_many_arguments)]
        fn aliasing_new_borrow<T>(
            enabled: bool,
            parent: u8,
            ptr: *const T,
            cell_mask: u64,
            freeze: bool,
            is_shared: bool,
            is_protected: bool,
            is_strong: bool,
        ) -> u8 {
            // The pointer is in an enum variant that is not the active one.
            if !enabled {
                return UNKNOWN_TAG;
            }
            let obj = super::mem::pointer_object(ptr);
            let offset = super::mem::pointer_offset(ptr);
            let size = size_of::<T>();
            aliasing_new_borrow_bytes(
                parent,
                obj,
                offset,
                size,
                cell_mask,
                freeze,
                is_shared,
                is_protected,
                is_strong,
            )
        }

        /// `aliasing_new_borrow_bytes` for a reference to the `size_of_val(ptr)` bytes at `ptr`,
        /// for an unsized `T`.
        #[kanitool::disable_checks(pointer)]
        #[kanitool::fn_marker = "AliasingNewBorrowUnsizedModel"]
        fn aliasing_new_borrow_unsized<T: MetaSized>(
            enabled: bool,
            parent: u8,
            ptr: *const T,
            freeze: bool,
            is_shared: bool,
            is_protected: bool,
            is_strong: bool,
        ) -> u8 {
            // The pointer is in an enum variant that is not the active one.
            if !enabled {
                return UNKNOWN_TAG;
            }
            let size = match super::mem::checked_size_of_raw(ptr) {
                Some(size) => size,
                None => 0,
            };
            let thin = ptr as *const u8;
            let obj = super::mem::pointer_object(thin);
            let offset = super::mem::pointer_offset(thin);
            aliasing_new_borrow_bytes(
                parent,
                obj,
                offset,
                size,
                0,
                freeze,
                is_shared,
                is_protected,
                is_strong,
            )
        }

        /// Deallocate `size` bytes at `ptr`, tagged `tag`.
        #[kanitool::disable_checks(pointer)]
        #[kanitool::fn_marker = "AliasingDeallocModel"]
        #[unsafe(export_name = "__VERIFIER_kani_aliasing_aliasing_dealloc")]
        fn aliasing_dealloc(tag: u8, ptr: *const u8, size: usize) -> u8 {
            let s = state();
            let obj = super::mem::pointer_object(ptr);
            let offset = super::mem::pointer_offset(ptr);
            if !monitor_covers(s, obj, offset, size) {
                return ACCESS_OK;
            }
            let code = monitor_dealloc(s, tag);
            code
        }

        /// Record that the pointer tagged `tag` was exposed.
        #[kanitool::disable_checks(pointer)]
        #[kanitool::fn_marker = "AliasingExposeModel"]
        #[unsafe(export_name = "__VERIFIER_kani_aliasing_aliasing_expose")]
        fn aliasing_expose(tag: u8) {
            monitor_expose(state(), tag);
        }

        /// Record the tags of the pointers in the arguments of a direct call to `callee`, in
        /// the order the compiler lists them.
        #[kanitool::disable_checks(pointer)]
        #[kanitool::fn_marker = "AliasingPushCallModel"]
        #[allow(clippy::too_many_arguments)]
        #[unsafe(export_name = "__VERIFIER_kani_aliasing_aliasing_push_call")]
        fn aliasing_push_call(
            callee: u64,
            tag0: u8,
            tag1: u8,
            tag2: u8,
            tag3: u8,
            tag4: u8,
            tag5: u8,
            tag6: u8,
            tag7: u8,
        ) {
            let c = calls();
            c.call_callee = callee;
            c.call_tags = [tag0, tag1, tag2, tag3, tag4, tag5, tag6, tag7];
        }

        /// The tag of the `index`-th pointer in the arguments of `callee`, if the pending call is
        /// a direct call to `callee`, or a call through `dyn` to the trait method `method` that
        /// `callee` implements (0 if none); the unknown tag otherwise.
        #[kanitool::disable_checks(pointer)]
        #[kanitool::fn_marker = "AliasingArgTagModel"]
        #[unsafe(export_name = "__VERIFIER_kani_aliasing_aliasing_arg_tag")]
        fn aliasing_arg_tag(callee: u64, method: u64, index: usize) -> u8 {
            let c = calls();
            let pending = c.call_callee;
            if pending != 0 && (pending == callee || pending == method) && index < MAX_ARG_TAGS {
                c.call_tags[index]
            } else {
                UNKNOWN_TAG
            }
        }

        /// Called once a function has read its argument tags.
        #[kanitool::disable_checks(pointer)]
        #[kanitool::fn_marker = "AliasingEndArgsModel"]
        #[unsafe(export_name = "__VERIFIER_kani_aliasing_aliasing_end_args")]
        fn aliasing_end_args() {
            calls().call_callee = 0;
        }

        /// The number of tags in use when a function starts, for `aliasing_return`.
        #[kanitool::disable_checks(pointer)]
        #[kanitool::fn_marker = "AliasingFrameEnterModel"]
        #[unsafe(export_name = "__VERIFIER_kani_aliasing_aliasing_frame_enter")]
        fn aliasing_frame_enter() -> u8 {
            state().count
        }

        /// Record the tags of the pointers in the value `callee` returns, and drop the tags
        /// `callee` created that nothing can reach anymore.
        ///
        /// Tags flow through locals, call arguments, returned values, and shadow memory, where
        /// `monitor_store` records the ones that may outlive the function. So once a function
        /// returns, the tags it created (`frame_count..count`) are unreachable, except the ones it
        /// returns or stored, which may need the tags created before them as ancestors.
        #[kanitool::disable_checks(pointer)]
        #[kanitool::fn_marker = "AliasingReturnModel"]
        #[unsafe(export_name = "__VERIFIER_kani_aliasing_aliasing_return")]
        fn aliasing_return(
            callee: u64,
            method: u64,
            frame_count: u8,
            tag0: u8,
            tag1: u8,
            tag2: u8,
            tag3: u8,
        ) {
            let c = calls();
            c.ret_callee = callee;
            c.ret_method = method;
            c.ret_tags = [tag0, tag1, tag2, tag3];
            monitor_return(state(), frame_count, [tag0, tag1, tag2, tag3]);
        }

        /// The protector of the argument tagged `tag` ends, before the function returns.
        #[kanitool::disable_checks(pointer)]
        #[kanitool::fn_marker = "AliasingEndProtectorModel"]
        #[unsafe(export_name = "__VERIFIER_kani_aliasing_aliasing_end_protector")]
        fn aliasing_end_protector(tag: u8) -> u8 {
            let code = monitor_end_protector(state(), tag);
            code
        }

        /// The tag of the `index`-th pointer in the value the call to `callee` (a function, or a
        /// trait method called through `dyn`) that just returned produced, if the function that
        /// returned recorded it; the unknown tag otherwise.
        #[kanitool::disable_checks(pointer)]
        #[kanitool::fn_marker = "AliasingRetTagModel"]
        #[unsafe(export_name = "__VERIFIER_kani_aliasing_aliasing_ret_tag")]
        fn aliasing_ret_tag(callee: u64, index: usize) -> u8 {
            let c = calls();
            if callee != 0
                && (c.ret_callee == callee || c.ret_method == callee)
                && index < MAX_RET_TAGS
            {
                c.ret_tags[index]
            } else {
                UNKNOWN_TAG
            }
        }

        /// Called once a caller has read the tags of a returned value.
        #[kanitool::disable_checks(pointer)]
        #[kanitool::fn_marker = "AliasingEndRetModel"]
        #[unsafe(export_name = "__VERIFIER_kani_aliasing_aliasing_end_ret")]
        fn aliasing_end_ret() {
            calls().ret_callee = 0;
            calls().ret_method = 0;
        }
    };
}
