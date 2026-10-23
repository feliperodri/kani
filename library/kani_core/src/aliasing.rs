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
        /// The tag of a pointer created from an integer (`ptr::with_exposed_provenance`): it may
        /// be any exposed tag.
        const EXPOSED_TAG: u8 = u8::MAX - 1;

        /// Results of `aliasing_access`, checked by the compiler-inserted assertions.
        const ACCESS_OK: u8 = 0;
        const ACCESS_INVALIDATED: u8 = 1;
        const ACCESS_WRITE_FROZEN: u8 = 2;
        const ACCESS_PROTECTOR: u8 = 3;
        const ACCESS_NOT_EXPOSED: u8 = 4;

        /// Number of pointers in the arguments, and in the returned value, of a direct call
        /// whose tags are passed between caller and callee.
        const MAX_ARG_TAGS: usize = 8;
        const MAX_RET_TAGS: usize = 4;

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
            /// Tags of reference arguments of functions that are still running.
            protected: u64,
            /// Tags whose permission at the tracked byte is initialized: the byte is in the range
            /// of the reference, or was accessed through the tag or one of its descendants.
            /// Protectors only apply to initialized permissions, as in Tree Borrows.
            initialized: u64,
            /// Shared references whose referent is inside an `UnsafeCell` at the tracked byte. As
            /// in Tree Borrows, such a reference is not retagged there: accesses through it are
            /// accesses through `alias`, its nearest ancestor that is not one of these.
            cell: u64,
            alias: [u8; MAX_TAGS as usize],
            /// Mutable references whose referent is inside an `UnsafeCell` at the tracked byte:
            /// until written, foreign writes do not disable them (Tree Borrows' "reserved, interior
            /// mutable").
            interior: u64,
            /// Tags whose pointer was exposed (cast to an integer with `expose_provenance`), and
            /// whether a pointer with an unknown tag was.
            exposed: u64,
            unknown_exposed: bool,
            /// Protected tags that were never written and saw a foreign read: writing through
            /// them is undefined behavior (Tree Borrows' "reserved, conflicted").
            conflicted: u64,
            /// Tags of the pointer arguments of the pending direct call, for the callee to pick
            /// up when its identifier matches.
            call_callee: u64,
            call_tags: [u8; MAX_ARG_TAGS],
            /// Tag of the pointer returned by the last instrumented function, and its identifier.
            ret_callee: u64,
            ret_tags: [u8; MAX_RET_TAGS],
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
            protected: 0,
            initialized: 0,
            cell: 0,
            alias: [0; MAX_TAGS as usize],
            interior: 0,
            exposed: 0,
            unknown_exposed: false,
            conflicted: 0,
            call_callee: 0,
            call_tags: [UNKNOWN_TAG; MAX_ARG_TAGS],
            ret_callee: 0,
            ret_tags: [UNKNOWN_TAG; MAX_RET_TAGS],
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
                ALIASING_STATE.protected = 0;
                ALIASING_STATE.initialized = 1;
                ALIASING_STATE.cell = 0;
                ALIASING_STATE.interior = 0;
                ALIASING_STATE.exposed = 0;
                ALIASING_STATE.unknown_exposed = false;
                ALIASING_STATE.conflicted = 0;
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
                if tag == EXPOSED_TAG {
                    return aliasing_wildcard_access(is_write);
                }
                if tag >= ALIASING_STATE.count {
                    super::unsupported(
                        "Kani's aliasing checks do not know which reference this pointer was \
                         derived from, so they cannot check this access",
                    );
                }
                let tag = if ALIASING_STATE.cell & (1u64 << tag) != 0 {
                    ALIASING_STATE.alias[tag as usize]
                } else {
                    tag
                };
                let bit = 1u64 << tag;
                let local = ALIASING_STATE.ancestors[tag as usize];
                if ALIASING_STATE.valid & bit == 0 {
                    return ACCESS_INVALIDATED;
                }
                let foreign = ALIASING_STATE.valid & !local;
                let protected = ALIASING_STATE.protected & ALIASING_STATE.initialized;
                if is_write {
                    // Shared references to an `UnsafeCell`'s bytes are transparent: they are
                    // never frozen, nor activated by writes through their descendants.
                    let opaque_local = local & !ALIASING_STATE.cell;
                    if ALIASING_STATE.frozen & opaque_local != 0 {
                        return ACCESS_WRITE_FROZEN;
                    }
                    // A write disables every foreign tag, which must not be protected, and
                    // activates the accessing tag and its ancestors, which must not be
                    // conflicted.
                    let disabled = foreign & !(ALIASING_STATE.interior & !ALIASING_STATE.active);
                    if protected & (disabled | (ALIASING_STATE.conflicted & local)) != 0 {
                        return ACCESS_PROTECTOR;
                    }
                    ALIASING_STATE.valid &= !disabled;
                    ALIASING_STATE.active |= opaque_local;
                } else {
                    // A read freezes every foreign tag that has been written through, and
                    // conflicts every protected foreign tag that has not.
                    ALIASING_STATE.frozen |= ALIASING_STATE.active & foreign;
                    ALIASING_STATE.conflicted |=
                        protected & foreign & !ALIASING_STATE.active & !ALIASING_STATE.frozen;
                }
                ALIASING_STATE.initialized |= local;
                ACCESS_OK
            }
        }

        /// An access to the tracked byte through a pointer created from an integer, as in Tree
        /// Borrows: it is allowed if some exposed tag allows it, and it only changes the tags
        /// that are foreign to every exposed tag that allows it.
        #[kanitool::disable_checks(pointer)]
        #[kanitool::fn_marker = "AliasingWildcardAccessModel"]
        fn aliasing_wildcard_access(is_write: bool) -> u8 {
            unsafe {
                if ALIASING_STATE.unknown_exposed {
                    super::unsupported(
                        "Kani's aliasing checks cannot check an access through a pointer created \
                         from an integer once a pointer whose tag they do not know was exposed",
                    );
                }
                let opaque_frozen = ALIASING_STATE.frozen & !ALIASING_STATE.cell;
                let mut possibly_local = 0u64;
                let mut allowed = false;
                // Written out instead of looping, so that a harness's unwinding bound does not
                // apply here, and without a closure, which would be instrumented like user code.
                let exposed = ALIASING_STATE.exposed & ALIASING_STATE.valid;
                if exposed & (1u64 << 0) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[0] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[0];
                }
                if exposed & (1u64 << 1) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[1] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[1];
                }
                if exposed & (1u64 << 2) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[2] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[2];
                }
                if exposed & (1u64 << 3) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[3] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[3];
                }
                if exposed & (1u64 << 4) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[4] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[4];
                }
                if exposed & (1u64 << 5) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[5] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[5];
                }
                if exposed & (1u64 << 6) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[6] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[6];
                }
                if exposed & (1u64 << 7) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[7] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[7];
                }
                if exposed & (1u64 << 8) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[8] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[8];
                }
                if exposed & (1u64 << 9) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[9] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[9];
                }
                if exposed & (1u64 << 10) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[10] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[10];
                }
                if exposed & (1u64 << 11) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[11] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[11];
                }
                if exposed & (1u64 << 12) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[12] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[12];
                }
                if exposed & (1u64 << 13) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[13] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[13];
                }
                if exposed & (1u64 << 14) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[14] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[14];
                }
                if exposed & (1u64 << 15) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[15] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[15];
                }
                if exposed & (1u64 << 16) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[16] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[16];
                }
                if exposed & (1u64 << 17) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[17] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[17];
                }
                if exposed & (1u64 << 18) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[18] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[18];
                }
                if exposed & (1u64 << 19) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[19] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[19];
                }
                if exposed & (1u64 << 20) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[20] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[20];
                }
                if exposed & (1u64 << 21) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[21] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[21];
                }
                if exposed & (1u64 << 22) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[22] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[22];
                }
                if exposed & (1u64 << 23) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[23] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[23];
                }
                if exposed & (1u64 << 24) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[24] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[24];
                }
                if exposed & (1u64 << 25) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[25] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[25];
                }
                if exposed & (1u64 << 26) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[26] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[26];
                }
                if exposed & (1u64 << 27) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[27] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[27];
                }
                if exposed & (1u64 << 28) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[28] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[28];
                }
                if exposed & (1u64 << 29) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[29] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[29];
                }
                if exposed & (1u64 << 30) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[30] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[30];
                }
                if exposed & (1u64 << 31) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[31] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[31];
                }
                if exposed & (1u64 << 32) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[32] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[32];
                }
                if exposed & (1u64 << 33) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[33] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[33];
                }
                if exposed & (1u64 << 34) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[34] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[34];
                }
                if exposed & (1u64 << 35) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[35] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[35];
                }
                if exposed & (1u64 << 36) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[36] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[36];
                }
                if exposed & (1u64 << 37) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[37] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[37];
                }
                if exposed & (1u64 << 38) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[38] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[38];
                }
                if exposed & (1u64 << 39) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[39] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[39];
                }
                if exposed & (1u64 << 40) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[40] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[40];
                }
                if exposed & (1u64 << 41) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[41] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[41];
                }
                if exposed & (1u64 << 42) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[42] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[42];
                }
                if exposed & (1u64 << 43) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[43] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[43];
                }
                if exposed & (1u64 << 44) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[44] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[44];
                }
                if exposed & (1u64 << 45) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[45] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[45];
                }
                if exposed & (1u64 << 46) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[46] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[46];
                }
                if exposed & (1u64 << 47) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[47] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[47];
                }
                if exposed & (1u64 << 48) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[48] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[48];
                }
                if exposed & (1u64 << 49) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[49] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[49];
                }
                if exposed & (1u64 << 50) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[50] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[50];
                }
                if exposed & (1u64 << 51) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[51] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[51];
                }
                if exposed & (1u64 << 52) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[52] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[52];
                }
                if exposed & (1u64 << 53) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[53] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[53];
                }
                if exposed & (1u64 << 54) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[54] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[54];
                }
                if exposed & (1u64 << 55) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[55] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[55];
                }
                if exposed & (1u64 << 56) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[56] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[56];
                }
                if exposed & (1u64 << 57) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[57] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[57];
                }
                if exposed & (1u64 << 58) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[58] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[58];
                }
                if exposed & (1u64 << 59) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[59] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[59];
                }
                if exposed & (1u64 << 60) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[60] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[60];
                }
                if exposed & (1u64 << 61) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[61] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[61];
                }
                if exposed & (1u64 << 62) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[62] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[62];
                }
                if exposed & (1u64 << 63) != 0
                    && (!is_write || opaque_frozen & ALIASING_STATE.ancestors[63] == 0)
                {
                    allowed = true;
                    possibly_local |= ALIASING_STATE.ancestors[63];
                }
                if !allowed {
                    return ACCESS_NOT_EXPOSED;
                }
                let foreign = ALIASING_STATE.valid & !possibly_local;
                let protected = ALIASING_STATE.protected & ALIASING_STATE.initialized;
                if is_write {
                    let disabled = foreign & !(ALIASING_STATE.interior & !ALIASING_STATE.active);
                    if protected & disabled != 0 {
                        return ACCESS_PROTECTOR;
                    }
                    ALIASING_STATE.valid &= !disabled;
                } else {
                    ALIASING_STATE.frozen |= ALIASING_STATE.active & foreign;
                    ALIASING_STATE.conflicted |=
                        protected & foreign & !ALIASING_STATE.active & !ALIASING_STATE.frozen;
                }
                ACCESS_OK
            }
        }

        /// Record that the pointer tagged `tag` was exposed.
        #[kanitool::disable_checks(pointer)]
        #[kanitool::fn_marker = "AliasingExposeModel"]
        fn aliasing_expose(tag: u8) {
            unsafe {
                if tag < ALIASING_STATE.count {
                    let tag = if ALIASING_STATE.cell & (1u64 << tag) != 0 {
                        ALIASING_STATE.alias[tag as usize]
                    } else {
                        tag
                    };
                    ALIASING_STATE.exposed |= 1u64 << tag;
                } else if tag != EXPOSED_TAG {
                    ALIASING_STATE.unknown_exposed = true;
                }
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

        /// Read the `size_of::<T>()` bytes at `ptr` through `tag`, except the bytes in
        /// `cell_mask` (bit `i` is byte `i`): the read that creating a shared reference to a type
        /// with an `UnsafeCell` performs, which does not touch the cell's bytes.
        #[kanitool::disable_checks(pointer)]
        #[kanitool::fn_marker = "AliasingReadOutsideCellsModel"]
        fn aliasing_read_outside_cells<T>(tag: u8, ptr: *const T, cell_mask: u64) -> u8 {
            let obj = super::mem::pointer_object(ptr);
            let offset = super::mem::pointer_offset(ptr);
            let in_cell = unsafe {
                ALIASING_STATE.tracked_object_id == obj
                    && ALIASING_STATE.tracked_offset >= offset
                    && ALIASING_STATE.tracked_offset - offset < 64
                    && (cell_mask >> (ALIASING_STATE.tracked_offset - offset)) & 1 != 0
            };
            if in_cell {
                return ACCESS_OK;
            }
            aliasing_access_bytes(tag, obj, offset, size_of::<T>(), false)
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

        /// Create a reference to `size` bytes at offset `offset` of object `obj` from a pointer
        /// tagged `parent`, and return the tag of the new reference, a child of `parent`. A
        /// protected reference is the retag of a reference argument when a function starts; it
        /// stays protected until the function returns.
        ///
        /// The read access that creating a reference performs is checked separately, before.
        #[kanitool::disable_checks(pointer)]
        #[kanitool::fn_marker = "AliasingNewBorrowBytesModel"]
        fn aliasing_new_borrow_bytes(
            parent: u8,
            obj: usize,
            offset: usize,
            size: usize,
            cell_mask: u64,
            is_shared: bool,
            is_protected: bool,
        ) -> u8 {
            unsafe {
                // The tag is created whether or not the reference covers the tracked byte: as in
                // Tree Borrows, a reference has a permission at every location of the
                // allocation, initialized lazily outside its range. Not depending on the
                // tracked byte keeps the number of tags concrete.
                if parent >= ALIASING_STATE.count {
                    return parent;
                }
                // Out of tags: accesses through the new reference to the tracked byte are
                // reported as unsupported.
                if ALIASING_STATE.count == MAX_TAGS {
                    return UNKNOWN_TAG;
                }
                let tag = ALIASING_STATE.count;
                let bit = 1u64 << tag;
                ALIASING_STATE.count += 1;
                ALIASING_STATE.ancestors[tag as usize] =
                    ALIASING_STATE.ancestors[parent as usize] | bit;
                ALIASING_STATE.valid |= bit;
                ALIASING_STATE.active &= !bit;
                ALIASING_STATE.conflicted &= !bit;
                let covers = ALIASING_STATE.tracked_object_id == obj
                    && ALIASING_STATE.tracked_offset >= offset
                    && ALIASING_STATE.tracked_offset - offset < size;
                // Whether the tracked byte is inside an `UnsafeCell` of the referent: bit `i` of
                // `cell_mask` is byte `i` of the referent.
                let in_cell = covers && {
                    let index = ALIASING_STATE.tracked_offset - offset;
                    index < 64 && (cell_mask >> index) & 1 != 0
                };
                if covers {
                    ALIASING_STATE.initialized |= bit;
                } else {
                    ALIASING_STATE.initialized &= !bit;
                }
                let parent_bit = 1u64 << parent;
                ALIASING_STATE.alias[tag as usize] = if is_shared && in_cell {
                    if ALIASING_STATE.cell & parent_bit != 0 {
                        ALIASING_STATE.alias[parent as usize]
                    } else {
                        parent
                    }
                } else {
                    tag
                };
                if is_shared && in_cell {
                    ALIASING_STATE.cell |= bit;
                } else {
                    ALIASING_STATE.cell &= !bit;
                }
                if !is_shared && in_cell {
                    ALIASING_STATE.interior |= bit;
                } else {
                    ALIASING_STATE.interior &= !bit;
                }
                if is_protected && !(is_shared && in_cell) {
                    ALIASING_STATE.protected |= bit;
                } else {
                    ALIASING_STATE.protected &= !bit;
                }
                if is_shared && !in_cell {
                    ALIASING_STATE.frozen |= bit;
                } else {
                    ALIASING_STATE.frozen &= !bit;
                }
                tag
            }
        }

        /// `aliasing_new_borrow_bytes` for a reference to the `size_of::<T>()` bytes at `ptr`.
        #[kanitool::disable_checks(pointer)]
        #[kanitool::fn_marker = "AliasingNewBorrowModel"]
        fn aliasing_new_borrow<T>(
            parent: u8,
            ptr: *const T,
            cell_mask: u64,
            is_shared: bool,
            is_protected: bool,
        ) -> u8 {
            let obj = super::mem::pointer_object(ptr);
            let offset = super::mem::pointer_offset(ptr);
            let size = size_of::<T>();
            aliasing_new_borrow_bytes(parent, obj, offset, size, cell_mask, is_shared, is_protected)
        }

        /// `aliasing_new_borrow_bytes` for a reference to the `size_of_val(ptr)` bytes at `ptr`,
        /// for an unsized `T`.
        #[kanitool::disable_checks(pointer)]
        #[kanitool::fn_marker = "AliasingNewBorrowUnsizedModel"]
        fn aliasing_new_borrow_unsized<T: MetaSized>(
            parent: u8,
            ptr: *const T,
            is_shared: bool,
            is_protected: bool,
        ) -> u8 {
            let size = match super::mem::checked_size_of_raw(ptr) {
                Some(size) => size,
                None => 0,
            };
            let thin = ptr as *const u8;
            let obj = super::mem::pointer_object(thin);
            let offset = super::mem::pointer_offset(thin);
            aliasing_new_borrow_bytes(parent, obj, offset, size, 0, is_shared, is_protected)
        }

        /// Deallocate `size` bytes at `ptr`. Deallocating memory that a reference argument of a
        /// running function points to is undefined behavior.
        #[kanitool::disable_checks(pointer)]
        #[kanitool::fn_marker = "AliasingDeallocModel"]
        fn aliasing_dealloc(ptr: *const u8, size: usize) -> u8 {
            let obj = super::mem::pointer_object(ptr);
            let offset = super::mem::pointer_offset(ptr);
            unsafe {
                let covers = ALIASING_STATE.tracked_object_id == obj
                    && ALIASING_STATE.tracked_offset >= offset
                    && ALIASING_STATE.tracked_offset - offset < size;
                if covers
                    && ALIASING_STATE.protected
                        & ALIASING_STATE.initialized
                        & ALIASING_STATE.valid
                        & !ALIASING_STATE.cell
                        != 0
                {
                    return ACCESS_PROTECTOR;
                }
            }
            ACCESS_OK
        }

        /// Record the tags of the pointers in the arguments of a direct call to `callee`, in
        /// the order the compiler lists them.
        #[kanitool::disable_checks(pointer)]
        #[kanitool::fn_marker = "AliasingPushCallModel"]
        #[allow(clippy::too_many_arguments)]
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
            unsafe {
                ALIASING_STATE.call_callee = callee;
                ALIASING_STATE.call_tags = [tag0, tag1, tag2, tag3, tag4, tag5, tag6, tag7];
            }
        }

        /// The tag of the `index`-th pointer in the arguments of `callee`, if the pending call is
        /// a direct call to `callee`; the unknown tag otherwise.
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

        /// Record the tags of the pointers in the value `callee` returns, and drop the tags
        /// `callee` created that nothing can reach anymore.
        ///
        /// Tags only flow through locals, the arguments of direct calls, and returned values; a
        /// pointer read from memory gets the unknown tag. So once a function returns, the tags
        /// it created (`frame_count..count`) are unreachable, except the ones it returns, which
        /// may need the tags created before them as ancestors. Tags created before the call are
        /// kept, as the caller may still hold them.
        #[kanitool::disable_checks(pointer)]
        #[kanitool::fn_marker = "AliasingReturnModel"]
        fn aliasing_return(callee: u64, frame_count: u8, tag0: u8, tag1: u8, tag2: u8, tag3: u8) {
            unsafe {
                ALIASING_STATE.ret_callee = callee;
                ALIASING_STATE.ret_tags = [tag0, tag1, tag2, tag3];
                // The function's reference arguments stop being protected.
                if frame_count < MAX_TAGS {
                    let kept = (1u64 << frame_count) - 1;
                    ALIASING_STATE.protected &= kept;
                    ALIASING_STATE.conflicted &= kept;
                }
                // No closure or loop here: a closure would be instrumented like user code, and
                // its own return would call this function again.
                let mut count = frame_count;
                if frame_count <= tag0 && tag0 < ALIASING_STATE.count && count <= tag0 {
                    count = tag0 + 1;
                }
                if frame_count <= tag1 && tag1 < ALIASING_STATE.count && count <= tag1 {
                    count = tag1 + 1;
                }
                if frame_count <= tag2 && tag2 < ALIASING_STATE.count && count <= tag2 {
                    count = tag2 + 1;
                }
                if frame_count <= tag3 && tag3 < ALIASING_STATE.count && count <= tag3 {
                    count = tag3 + 1;
                }
                if count < ALIASING_STATE.count {
                    ALIASING_STATE.count = count;
                }
            }
        }

        /// The tag of the `index`-th pointer in the value the call to `callee` that just
        /// returned produced, if `callee` recorded it; the unknown tag otherwise.
        #[kanitool::disable_checks(pointer)]
        #[kanitool::fn_marker = "AliasingRetTagModel"]
        fn aliasing_ret_tag(callee: u64, index: usize) -> u8 {
            unsafe {
                if ALIASING_STATE.ret_callee == callee && index < MAX_RET_TAGS {
                    ALIASING_STATE.ret_tags[index]
                } else {
                    UNKNOWN_TAG
                }
            }
        }

        /// Called once a caller has read the tags of a returned value.
        #[kanitool::disable_checks(pointer)]
        #[kanitool::fn_marker = "AliasingEndRetModel"]
        fn aliasing_end_ret() {
            unsafe {
                ALIASING_STATE.ret_callee = 0;
            }
        }
    };
}
