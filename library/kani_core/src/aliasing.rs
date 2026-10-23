// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Runtime model of the aliasing checks (`-Z aliasing-checks`).
//!
//! This is the common core of Stacked Borrows and Tree Borrows: only the rules both models agree
//! on, so that whatever this model rejects is undefined behavior under either of them. It is built
//! around tags, ancestry and an abstract permission state, not around a borrow stack, so that the
//! Tree Borrows state machine can later refine it.
//!
//! - Every reference created by a reborrow (`&place`, `&mut place`) gets a fresh tag whose parent
//!   is the tag of the pointer the place was reached through (or the root tag of the allocation).
//!   Raw pointers keep the tag of the pointer they were derived from, as in Tree Borrows.
//! - A tag is *valid* until a conflicting access disables it, *active* once memory was written
//!   through it or one of its descendants, and *frozen* if it is a shared reference or if it was
//!   active when a foreign read happened.
//! - An access through a tag is *local* to the tag's ancestors (and the tag itself) and *foreign*
//!   to every other tag.
//! - Rules: accessing through an invalid tag is UB; writing through a tag with a frozen ancestor
//!   (or a frozen tag) is UB; a write disables every foreign tag; a read freezes every foreign tag
//!   that is active; creating a reference reads the referenced memory through the parent tag.
//!
//! Like the memory-initialization checks, the state is tracked for a single byte of memory,
//! chosen non-deterministically for each harness: if some byte is accessed in a way the rules
//! reject, there is a choice that tracks that byte. The compiler inserts calls to the functions
//! below; see `kani_middle::transform::check_aliasing`.

// Definitions in this module are not meant to be visible to the end user, only the compiler.
#![allow(dead_code)]

#[macro_export]
#[allow(clippy::crate_in_macro_def)]
macro_rules! kani_aliasing {
    ($core:tt) => {
        use $core::marker::MetaSized;

        /// Maximum number of tags (references to the tracked byte) alive at once, including the
        /// root. See `aliasing_new_borrow` for what happens beyond.
        const MAX_TAGS: u8 = 64;
        /// The tag of the allocation itself: direct accesses to a local and accesses through a
        /// `Box` use it.
        const ROOT_TAG: u8 = 0;
        /// The tag of a pointer whose provenance the instrumentation does not know (for instance
        /// a pointer read from memory, or returned by an indirect call). An access through it to
        /// the tracked byte is reported as unsupported: the checks cannot decide it.
        const UNKNOWN_TAG: u8 = u8::MAX;

        /// Results of `aliasing_access`, checked by the compiler-inserted assertions.
        const ACCESS_OK: u8 = 0;
        const ACCESS_INVALIDATED: u8 = 1;
        const ACCESS_WRITE_FROZEN: u8 = 2;

        /// Number of pointer arguments whose tags are passed to direct callees.
        const MAX_ARG_TAGS: usize = 4;

        struct AliasingState {
            tracked_object_id: usize,
            tracked_offset: usize,
            /// Number of tags in use; tags are `0..count`.
            count: u8,
            /// For each tag, the bit set of its ancestors, including itself.
            ancestors: [u64; MAX_TAGS as usize],
            /// Bit sets over tags.
            valid: u64,
            active: u64,
            frozen: u64,
            /// Tags of the pointer arguments of the pending direct call, for the callee to pick
            /// up when its identifier matches.
            call_callee: u64,
            call_tags: [u8; MAX_ARG_TAGS],
            /// Tag of the pointer returned by the last instrumented function, and its identifier.
            ret_callee: u64,
            ret_tag: u8,
        }

        /// Global aliasing state. Set up by `aliasing_initialize` at the start of the harness.
        static mut ALIASING_STATE: AliasingState = AliasingState {
            tracked_object_id: 0,
            tracked_offset: 0,
            count: 1,
            ancestors: [0; MAX_TAGS as usize],
            valid: 0,
            active: 0,
            frozen: 0,
            call_callee: 0,
            call_tags: [UNKNOWN_TAG; MAX_ARG_TAGS],
            ret_callee: 0,
            ret_tag: UNKNOWN_TAG,
        };

        /// Choose the tracked byte and give it a root tag that is valid and active.
        #[kanitool::disable_checks(pointer)]
        #[kanitool::fn_marker = "AliasingInitializeModel"]
        fn aliasing_initialize() {
            unsafe {
                ALIASING_STATE.tracked_object_id = super::any();
                ALIASING_STATE.tracked_offset = super::any();
                ALIASING_STATE.count = 1;
                ALIASING_STATE.ancestors[ROOT_TAG as usize] = 1;
                ALIASING_STATE.valid = 1;
                ALIASING_STATE.active = 1;
                ALIASING_STATE.frozen = 0;
                ALIASING_STATE.call_callee = 0;
                ALIASING_STATE.ret_callee = 0;
            }
        }

        /// Access `size` bytes at offset `offset` of object `obj` through `tag`, and update the
        /// state of the tracked byte if the access covers it. Return `ACCESS_OK` or the rule it
        /// breaks.
        #[kanitool::disable_checks(pointer)]
        #[kanitool::fn_marker = "AliasingAccessBytesModel"]
        fn aliasing_access_bytes(
            tag: u8,
            obj: usize,
            offset: usize,
            size: usize,
            is_write: bool,
        ) -> u8 {
            unsafe {
                if ALIASING_STATE.tracked_object_id != obj
                    || ALIASING_STATE.tracked_offset < offset
                    || ALIASING_STATE.tracked_offset - offset >= size
                {
                    return ACCESS_OK;
                }
                if tag >= ALIASING_STATE.count {
                    super::unsupported(
                        "Kani's aliasing checks do not know which reference this pointer was \
                         derived from, so they cannot check this access",
                    );
                }
                let bit = 1u64 << tag;
                let local = ALIASING_STATE.ancestors[tag as usize];
                if ALIASING_STATE.valid & bit == 0 {
                    return ACCESS_INVALIDATED;
                }
                if is_write {
                    if ALIASING_STATE.frozen & local != 0 {
                        return ACCESS_WRITE_FROZEN;
                    }
                    // A write disables every foreign tag and activates the accessing tag and its
                    // ancestors.
                    ALIASING_STATE.valid &= local;
                    ALIASING_STATE.active |= local;
                } else {
                    // A read freezes every foreign tag that has been written through.
                    ALIASING_STATE.frozen |= ALIASING_STATE.active & !local;
                }
                ACCESS_OK
            }
        }

        /// Access the `size_of::<T>()` bytes at `ptr` through `tag`.
        #[kanitool::disable_checks(pointer)]
        #[kanitool::fn_marker = "AliasingAccessModel"]
        fn aliasing_access<T>(tag: u8, ptr: *const T, is_write: bool) -> u8 {
            let obj = super::mem::pointer_object(ptr);
            let offset = super::mem::pointer_offset(ptr);
            aliasing_access_bytes(tag, obj, offset, size_of::<T>(), is_write)
        }

        /// Access the `size_of_val(ptr)` bytes at `ptr` through `tag`, for an unsized `T`.
        #[kanitool::disable_checks(pointer)]
        #[kanitool::fn_marker = "AliasingAccessUnsizedModel"]
        fn aliasing_access_unsized<T: MetaSized>(tag: u8, ptr: *const T, is_write: bool) -> u8 {
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

        /// Create a reference from a pointer tagged `parent`, and return the tag of the new
        /// reference, a child of `parent`.
        ///
        /// The read access that creating a reference performs is checked separately, before.
        #[kanitool::disable_checks(pointer)]
        #[kanitool::fn_marker = "AliasingNewBorrowModel"]
        fn aliasing_new_borrow(parent: u8, is_shared: bool) -> u8 {
            unsafe {
                // The tag is created whether or not the reference covers the tracked byte: as in
                // Tree Borrows, a reference has a permission at every location of the
                // allocation, initialized lazily outside its range (the read that creating a
                // reference performs is checked separately, and only inside the range). Not
                // depending on the tracked byte keeps the number of tags concrete.
                if parent >= ALIASING_STATE.count {
                    return parent;
                }
                let parent_mask = ALIASING_STATE.ancestors[parent as usize];
                // Out of tags: accesses through the new reference to the tracked byte are
                // reported as unsupported.
                if ALIASING_STATE.count == MAX_TAGS {
                    return UNKNOWN_TAG;
                }
                let tag = ALIASING_STATE.count;
                let bit = 1u64 << tag;
                ALIASING_STATE.count += 1;
                ALIASING_STATE.ancestors[tag as usize] = parent_mask | bit;
                ALIASING_STATE.valid |= bit;
                ALIASING_STATE.active &= !bit;
                if is_shared {
                    ALIASING_STATE.frozen |= bit;
                } else {
                    ALIASING_STATE.frozen &= !bit;
                }
                tag
            }
        }

        /// Record the tags of the pointer arguments of a direct call to `callee`.
        #[kanitool::disable_checks(pointer)]
        #[kanitool::fn_marker = "AliasingPushCallModel"]
        fn aliasing_push_call(callee: u64, tag0: u8, tag1: u8, tag2: u8, tag3: u8) {
            unsafe {
                ALIASING_STATE.call_callee = callee;
                ALIASING_STATE.call_tags = [tag0, tag1, tag2, tag3];
            }
        }

        /// The tag of the `index`-th pointer argument of `callee`, if the pending call is a
        /// direct call to `callee`; the wildcard tag otherwise.
        #[kanitool::disable_checks(pointer)]
        #[kanitool::fn_marker = "AliasingArgTagModel"]
        fn aliasing_arg_tag(callee: u64, index: usize) -> u8 {
            unsafe {
                if ALIASING_STATE.call_callee == callee && index < MAX_ARG_TAGS {
                    ALIASING_STATE.call_tags[index]
                } else {
                    UNKNOWN_TAG
                }
            }
        }

        /// Called once a function has read its argument tags.
        #[kanitool::disable_checks(pointer)]
        #[kanitool::fn_marker = "AliasingEndArgsModel"]
        fn aliasing_end_args() {
            unsafe {
                ALIASING_STATE.call_callee = 0;
            }
        }

        /// The number of tags in use when a function starts, for `aliasing_return`.
        #[kanitool::disable_checks(pointer)]
        #[kanitool::fn_marker = "AliasingFrameEnterModel"]
        fn aliasing_frame_enter() -> u8 {
            unsafe { ALIASING_STATE.count }
        }

        /// Record the tag of the pointer `callee` returns, and drop the tags `callee` created that
        /// nothing can reach anymore.
        ///
        /// Tags only flow through locals, the arguments of direct calls, and returned pointers;
        /// a pointer read from memory gets the wildcard tag. So once a function returns, the tags
        /// it created (`frame_count..count`) are unreachable, except the one it returns, which
        /// may need the tags created before it as ancestors. Tags created before the call are
        /// kept, as the caller may still hold them.
        #[kanitool::disable_checks(pointer)]
        #[kanitool::fn_marker = "AliasingReturnModel"]
        fn aliasing_return(callee: u64, frame_count: u8, tag: u8) {
            unsafe {
                ALIASING_STATE.ret_callee = callee;
                ALIASING_STATE.ret_tag = tag;
                if frame_count <= tag && tag < ALIASING_STATE.count {
                    ALIASING_STATE.count = tag + 1;
                } else if frame_count < ALIASING_STATE.count {
                    ALIASING_STATE.count = frame_count;
                }
            }
        }

        /// The tag of the pointer the call to `callee` that just returned produced, if `callee`
        /// recorded it; the wildcard tag otherwise.
        #[kanitool::disable_checks(pointer)]
        #[kanitool::fn_marker = "AliasingTakeRetModel"]
        fn aliasing_take_ret(callee: u64) -> u8 {
            unsafe {
                let tag = if ALIASING_STATE.ret_callee == callee {
                    ALIASING_STATE.ret_tag
                } else {
                    UNKNOWN_TAG
                };
                ALIASING_STATE.ret_callee = 0;
                tag
            }
        }
    };
}
