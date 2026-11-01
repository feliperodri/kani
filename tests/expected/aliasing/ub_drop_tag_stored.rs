// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks
//! A reference passed to a call is dropped when the call returns, unless the callee stored it.
//! Here it is stored in memory, so its tag must survive and the later use must be checked.

fn stash<'a>(x: &'a mut u8, slot: &mut Option<&'a mut u8>) {
    *slot = Some(x);
}

#[kani::proof]
fn ub_drop_tag_stored() {
    let mut a = 0u8;
    let p = &mut a as *mut u8;
    let mut slot = None;
    stash(unsafe { &mut *p }, &mut slot);
    unsafe { *p = 1 };
    if let Some(r) = slot {
        *r = 2;
    }
}
