// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

// The transition core of the aliasing checks (`-Z aliasing-checks`).
//
// This macro generates the state of the aliasing monitor for the one tracked byte and the pure
// functions that update it. It has no statics, pointers or Kani hooks: `kani_aliasing!` keeps the
// global state and turns pointers into the booleans these functions take.
//
// The same code is verified with Verus (`library/kani_core/verus`): the Verus crate includes
// this file and expands this macro, and the `verus_verify` / `verus_spec` attributes below only
// exist when Verus compiles it (`verus_keep_ghost`). A normal build ignores them.
//
// State, for the tags `0..count` (tag 0 is the root of the allocation):
// - `ancestors[t]`: the bit set of the ancestors of `t`, including `t`.
// - `valid`, `active`, `frozen`, `conflicted`, `interior`: Tree Borrows' permission of each tag at
//   the tracked byte, as bits. Not valid is Disabled; valid and frozen is Frozen; valid, active
//   and not frozen is Active; otherwise Reserved, conflicted or interior-mutable per its bits.
// - `protected`, `initialized`: the tag is a protected reference argument; its permission at the
//   tracked byte is initialized (Tree Borrows initializes lazily).
// - `cell`, `alias`: shared references to the bytes of an `UnsafeCell`. Tree Borrows does not
//   retag those bytes, so such a tag has no permission of its own: accesses through it are
//   accesses through `alias[t]`, its nearest ancestor that is not one of these, and no access
//   changes it.
// - `exposed`, `unknown_exposed`: tags whose pointer was exposed, and whether a pointer with an
//   unknown tag was.

#[macro_export]
macro_rules! kani_aliasing_monitor {
    () => {
        /// Maximum number of tags alive at once, including the root.
        #[cfg_attr(verus_keep_ghost, verus_verify)]
        pub const MAX_TAGS: u8 = 64;
        /// The tag of the allocation itself.
        #[cfg_attr(verus_keep_ghost, verus_verify)]
        pub const ROOT_TAG: u8 = 0;
        /// The tag of a pointer whose provenance the instrumentation does not know.
        #[cfg_attr(verus_keep_ghost, verus_verify)]
        pub const UNKNOWN_TAG: u8 = u8::MAX;
        /// The tag of a pointer created from an integer: it may be any exposed tag.
        #[cfg_attr(verus_keep_ghost, verus_verify)]
        pub const EXPOSED_TAG: u8 = u8::MAX - 1;

        /// Results of an access. The compiler-inserted assertions check the first five; the
        /// wrappers report the last two as unsupported.
        #[cfg_attr(verus_keep_ghost, verus_verify)]
        pub const ACCESS_OK: u8 = 0;
        #[cfg_attr(verus_keep_ghost, verus_verify)]
        pub const ACCESS_INVALIDATED: u8 = 1;
        #[cfg_attr(verus_keep_ghost, verus_verify)]
        pub const ACCESS_WRITE_FROZEN: u8 = 2;
        #[cfg_attr(verus_keep_ghost, verus_verify)]
        pub const ACCESS_PROTECTOR: u8 = 3;
        #[cfg_attr(verus_keep_ghost, verus_verify)]
        pub const ACCESS_NOT_EXPOSED: u8 = 4;
        #[cfg_attr(verus_keep_ghost, verus_verify)]
        pub const ACCESS_UNKNOWN_TAG: u8 = 5;
        #[cfg_attr(verus_keep_ghost, verus_verify)]
        pub const ACCESS_UNKNOWN_EXPOSED: u8 = 6;

        #[cfg_attr(verus_keep_ghost, verus_verify)]
        pub struct MonitorState {
            pub tracked_object_id: usize,
            pub tracked_offset: usize,
            pub count: u8,
            pub ancestors: [u64; 64],
            pub valid: u64,
            pub active: u64,
            pub frozen: u64,
            pub conflicted: u64,
            pub interior: u64,
            pub protected: u64,
            pub initialized: u64,
            pub cell: u64,
            pub alias: [u8; 64],
            pub exposed: u64,
            pub unknown_exposed: bool,
        }

        /// The state before the harness chooses the tracked byte.
        #[cfg_attr(verus_keep_ghost, verus_verify)]
        #[cfg_attr(verus_keep_ghost, verus_verify)]
        pub const fn monitor_new() -> MonitorState {
            MonitorState {
                tracked_object_id: 0,
                tracked_offset: 0,
                count: 1,
                ancestors: [1; 64],
                valid: 1,
                active: 1,
                frozen: 0,
                conflicted: 0,
                interior: 0,
                protected: 0,
                initialized: 1,
                cell: 0,
                alias: [0; 64],
                exposed: 0,
                unknown_exposed: false,
            }
        }

        /// Track the byte at `offset` of object `obj`, with a single root tag that is valid,
        /// active and initialized.
        #[cfg_attr(verus_keep_ghost, verus_verify)]
        #[cfg_attr(verus_keep_ghost, verus_spec(
            ensures monitor_wf(&*final(s)), initial_spec(abstraction(&*final(s)))
        ))]
        pub fn monitor_initialize(s: &mut MonitorState, obj: usize, offset: usize) {
            s.tracked_object_id = obj;
            s.tracked_offset = offset;
            s.count = 1;
            s.ancestors[0] = 1;
            s.valid = 1;
            s.active = 1;
            s.frozen = 0;
            s.conflicted = 0;
            s.interior = 0;
            s.protected = 0;
            s.initialized = 1;
            s.cell = 0;
            s.alias[0] = 0;
            s.exposed = 0;
            s.unknown_exposed = false;
            #[cfg(verus_keep_ghost)]
            proof! { lemma_initialize(*s); }
        }

        /// Whether the `size` bytes at `offset` of object `obj` contain the tracked byte.
        #[cfg_attr(verus_keep_ghost, verus_verify)]
        pub fn monitor_covers(s: &MonitorState, obj: usize, offset: usize, size: usize) -> bool {
            s.tracked_object_id == obj
                && s.tracked_offset >= offset
                && s.tracked_offset - offset < size
        }

        /// An access to the tracked byte through `tag`: check it against the permissions of the
        /// tags on its path from the root, and apply Tree Borrows' transitions to every tag.
        #[cfg_attr(verus_keep_ghost, verus_verify)]
        #[cfg_attr(verus_keep_ghost, verus_spec(r =>
            requires monitor_wf(&*old(s)), tag < old(s).count,
            ensures access_refines(abstraction(&*old(s)), abstraction(&*final(s)), tag as nat,
                                   is_write, r),
                    monitor_wf(&*final(s)),
        ))]
        pub fn monitor_access(s: &mut MonitorState, tag: u8, is_write: bool) -> u8 {
            #[cfg(verus_keep_ghost)]
            proof_decl! { let ghost s0 = *s; let ghost t0 = tag; }
            let tag = if s.cell & (1u64 << tag) != 0 { s.alias[tag as usize] } else { tag };
            #[cfg(verus_keep_ghost)]
            proof! { lemma_access_eff(s0, t0, tag); }
            let local = s.ancestors[tag as usize] & !s.cell;
            if s.valid & local != local {
                #[cfg(verus_keep_ghost)]
                proof! { lemma_access_ub_invalid(s0, t0, tag, is_write); }
                return ACCESS_INVALIDATED;
            }
            let foreign = s.valid & !s.ancestors[tag as usize] & !s.cell;
            let protected = s.protected & s.initialized;
            if is_write {
                if s.frozen & local != 0 {
                    #[cfg(verus_keep_ghost)]
                    proof! { lemma_access_ub_frozen(s0, t0, tag); }
                    return ACCESS_WRITE_FROZEN;
                }
                let disabled = foreign & !(s.interior & !s.active);
                if protected & (disabled | (s.conflicted & local)) != 0 {
                    #[cfg(verus_keep_ghost)]
                    proof! { lemma_access_ub_protector(s0, t0, tag); }
                    return ACCESS_PROTECTOR;
                }
                s.valid = s.valid & !disabled;
                s.active = s.active | local;
            } else {
                s.conflicted = s.conflicted | (protected & foreign & !s.active & !s.frozen);
                s.frozen = s.frozen | (s.active & foreign);
            }
            s.initialized = s.initialized | local;
            #[cfg(verus_keep_ghost)]
            proof! { lemma_access_ok(s0, *s, t0, tag, is_write); }
            ACCESS_OK
        }

        /// Create a reference from a pointer tagged `parent` and return its tag. `covers`: the
        /// reference's range contains the tracked byte; `in_cell`: the byte is inside an
        /// `UnsafeCell` of the referent. Out of tags, the new reference gets the unknown tag.
        #[cfg_attr(verus_keep_ghost, verus_verify)]
        #[cfg_attr(verus_keep_ghost, verus_spec(r =>
            requires monitor_wf(&*old(s)),
            ensures monitor_wf(&*final(s)),
                    retag_spec(abstraction(&*old(s)), abstraction(&*final(s)), parent as nat,
                               covers, in_cell, is_shared, is_protected, r as nat),
        ))]
        pub fn monitor_new_borrow(
            s: &mut MonitorState,
            parent: u8,
            covers: bool,
            in_cell: bool,
            is_shared: bool,
            is_protected: bool,
        ) -> u8 {
            if parent >= s.count {
                return parent;
            }
            if s.count == MAX_TAGS {
                return UNKNOWN_TAG;
            }
            #[cfg(verus_keep_ghost)]
            proof_decl! { let ghost s0 = *s; }
            let tag = s.count;
            let bit = 1u64 << tag;
            let is_cell = is_shared && in_cell && covers;
            s.count = s.count + 1;
            s.ancestors[tag as usize] = s.ancestors[parent as usize] | bit;
            s.valid = s.valid | bit;
            s.active = s.active & !bit;
            s.conflicted = s.conflicted & !bit;
            s.exposed = s.exposed & !bit;
            s.alias[tag as usize] = if is_cell {
                if s.cell & (1u64 << parent) != 0 { s.alias[parent as usize] } else { parent }
            } else {
                tag
            };
            s.cell = if is_cell { s.cell | bit } else { s.cell & !bit };
            s.interior =
                if !is_shared && in_cell && covers { s.interior | bit } else { s.interior & !bit };
            s.initialized =
                if covers && !is_cell { s.initialized | bit } else { s.initialized & !bit };
            s.protected =
                if is_protected && !is_cell { s.protected | bit } else { s.protected & !bit };
            s.frozen = if is_shared && !is_cell { s.frozen | bit } else { s.frozen & !bit };
            #[cfg(verus_keep_ghost)]
            proof! {
                lemma_new_borrow(s0, *s, parent, covers, in_cell, is_shared, is_protected);
            }
            tag
        }

        /// Deallocating memory that contains the tracked byte: undefined behavior if a protected
        /// reference argument has an initialized permission there.
        #[cfg_attr(verus_keep_ghost, verus_verify)]
        #[cfg_attr(verus_keep_ghost, verus_spec(r =>
            requires monitor_wf(s),
            ensures (r == ACCESS_PROTECTOR) == dealloc_ub(abstraction(s)),
                    r == ACCESS_PROTECTOR || r == ACCESS_OK,
        ))]
        pub fn monitor_dealloc(s: &MonitorState) -> u8 {
            #[cfg(verus_keep_ghost)]
            proof! { lemma_dealloc(*s); }
            if s.protected & s.initialized & s.valid & !s.cell != 0 {
                ACCESS_PROTECTOR
            } else {
                ACCESS_OK
            }
        }

        /// Record that the pointer tagged `tag` was exposed.
        #[cfg_attr(verus_keep_ghost, verus_verify)]
        #[cfg_attr(verus_keep_ghost, verus_spec(
            requires monitor_wf(&*old(s)),
            ensures monitor_wf(&*final(s)),
                    expose_spec(abstraction(&*old(s)), abstraction(&*final(s)), tag as nat),
        ))]
        pub fn monitor_expose(s: &mut MonitorState, tag: u8) {
            if tag < s.count {
                #[cfg(verus_keep_ghost)]
                proof_decl! { let ghost s0 = *s; }
                let e = if s.cell & (1u64 << tag) != 0 { s.alias[tag as usize] } else { tag };
                #[cfg(verus_keep_ghost)]
                proof! { lemma_access_eff(s0, tag, e); }
                s.exposed = s.exposed | (1u64 << e);
                #[cfg(verus_keep_ghost)]
                proof! { lemma_expose(s0, *s, tag, e); }
            } else if tag != EXPOSED_TAG {
                s.unknown_exposed = true;
            }
        }

        /// One exposed tag `e` considered by `monitor_wildcard_access`: if it allows the access,
        /// add its path to `possibly_local`.
        #[cfg_attr(verus_keep_ghost, verus_verify)]
        #[cfg_attr(verus_keep_ghost, verus_spec(
            requires e < 64,
                     *old(allowed) == allowed_upto(s, is_write, e as nat),
                     *old(possibly_local) == local_upto(s, is_write, e as nat),
            ensures *final(allowed) == allowed_upto(s, is_write, (e + 1) as nat),
                    *final(possibly_local) == local_upto(s, is_write, (e + 1) as nat),
        ))]
        pub fn monitor_wildcard_candidate(
            s: &MonitorState,
            e: usize,
            is_write: bool,
            allowed: &mut bool,
            possibly_local: &mut u64,
        ) {
            #[cfg(verus_keep_ghost)]
            proof! { lemma_or_zero(*possibly_local); }
            let path = s.ancestors[e] & !s.cell;
            if s.exposed & s.valid & (1u64 << e) != 0
                && s.valid & path == path
                && (!is_write || s.frozen & path == 0)
            {
                *allowed = true;
                *possibly_local = *possibly_local | s.ancestors[e];
            }
        }

        /// An access to the tracked byte through a pointer created from an integer, as in Tree
        /// Borrows: allowed if some exposed tag allows it; it only changes the tags that are
        /// foreign to every exposed tag that allows it.
        #[cfg_attr(verus_keep_ghost, verus_verify)]
        #[cfg_attr(verus_keep_ghost, verus_spec(r =>
            requires monitor_wf(&*old(s)),
            ensures monitor_wf(&*final(s)),
                    wildcard_refines(abstraction(&*old(s)), abstraction(&*final(s)), is_write, r),
        ))]
        pub fn monitor_wildcard_access(s: &mut MonitorState, is_write: bool) -> u8 {
            if s.unknown_exposed {
                return ACCESS_UNKNOWN_EXPOSED;
            }
            #[cfg(verus_keep_ghost)]
            proof_decl! { let ghost s0 = *s; }
            let mut allowed = false;
            let mut possibly_local = 0u64;
            // Written out instead of looping, so that a harness's unwinding bound does not apply.
            monitor_wildcard_candidate(&*s, 0, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 1, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 2, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 3, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 4, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 5, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 6, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 7, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 8, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 9, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 10, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 11, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 12, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 13, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 14, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 15, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 16, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 17, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 18, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 19, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 20, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 21, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 22, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 23, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 24, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 25, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 26, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 27, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 28, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 29, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 30, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 31, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 32, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 33, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 34, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 35, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 36, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 37, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 38, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 39, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 40, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 41, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 42, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 43, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 44, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 45, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 46, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 47, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 48, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 49, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 50, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 51, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 52, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 53, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 54, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 55, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 56, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 57, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 58, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 59, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 60, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 61, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 62, is_write, &mut allowed, &mut possibly_local);
            monitor_wildcard_candidate(&*s, 63, is_write, &mut allowed, &mut possibly_local);

            if !allowed {
                #[cfg(verus_keep_ghost)]
                proof! { lemma_wildcard(s0, *s, is_write, possibly_local, ACCESS_NOT_EXPOSED); }
                return ACCESS_NOT_EXPOSED;
            }
            let foreign = s.valid & !possibly_local & !s.cell;
            let protected = s.protected & s.initialized;
            if is_write {
                let disabled = foreign & !(s.interior & !s.active);
                if protected & disabled != 0 {
                    #[cfg(verus_keep_ghost)]
                    proof! { lemma_wildcard(s0, *s, is_write, possibly_local, ACCESS_PROTECTOR); }
                    return ACCESS_PROTECTOR;
                }
                s.valid = s.valid & !disabled;
            } else {
                s.conflicted = s.conflicted | (protected & foreign & !s.active & !s.frozen);
                s.frozen = s.frozen | (s.active & foreign);
            }
            #[cfg(verus_keep_ghost)]
            proof! { lemma_wildcard(s0, *s, is_write, possibly_local, ACCESS_OK); }
            ACCESS_OK
        }

        /// A function that started with `frame_count` tags returns the tags in `kept`: its
        /// reference arguments stop being protected, and the tags it created are dropped, except
        /// the returned ones and the tags created before them.
        #[cfg_attr(verus_keep_ghost, verus_verify)]
        #[cfg_attr(verus_keep_ghost, verus_spec(
            requires monitor_wf(&*old(s)), frame_count >= 1,
            ensures monitor_wf(&*final(s)),
                    return_spec(abstraction(&*old(s)), abstraction(&*final(s)),
                                frame_count as nat, kept@),
        ))]
        pub fn monitor_return(s: &mut MonitorState, frame_count: u8, kept: [u8; 4]) {
            #[cfg(verus_keep_ghost)]
            proof_decl! { let ghost s0 = *s; }
            if frame_count < MAX_TAGS {
                #[cfg(verus_keep_ghost)]
                proof! { lemma_shift_pos(frame_count as u64); }
                let below = (1u64 << frame_count) - 1;
                s.protected = s.protected & below;
                s.conflicted = s.conflicted & below;
            }
            #[cfg(verus_keep_ghost)]
            proof_decl! { let ghost s1 = *s; }
            let mut count = frame_count;
            if frame_count <= kept[0] && kept[0] < s.count && count <= kept[0] {
                count = kept[0] + 1;
            }
            if frame_count <= kept[1] && kept[1] < s.count && count <= kept[1] {
                count = kept[1] + 1;
            }
            if frame_count <= kept[2] && kept[2] < s.count && count <= kept[2] {
                count = kept[2] + 1;
            }
            if frame_count <= kept[3] && kept[3] < s.count && count <= kept[3] {
                count = kept[3] + 1;
            }
            if count < s.count {
                s.count = count;
                // Forget the dropped tags entirely: a stale bit above `count` would otherwise
                // make a dropped tag look valid or exposed to `monitor_wildcard_access`.
                #[cfg(verus_keep_ghost)]
                proof! { lemma_shift_pos(count as u64); }
                let below = (1u64 << count) - 1;
                s.valid = s.valid & below;
                s.active = s.active & below;
                s.frozen = s.frozen & below;
                s.conflicted = s.conflicted & below;
                s.interior = s.interior & below;
                s.protected = s.protected & below;
                s.initialized = s.initialized & below;
                s.cell = s.cell & below;
                s.exposed = s.exposed & below;
            }
            #[cfg(verus_keep_ghost)]
            proof! { lemma_return(s0, s1, *s, frame_count, kept, count); }
        }
    };
}
