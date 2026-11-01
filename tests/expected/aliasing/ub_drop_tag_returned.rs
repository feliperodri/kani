// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks
//! A reference passed to a call is dropped when the call returns, unless the callee returned it.
//! Here it is returned, so its tag must survive and the later use must be checked.

fn id(x: &mut u8) -> &mut u8 {
    x
}

#[kani::proof]
fn ub_drop_tag_returned() {
    let mut a = 0u8;
    let p = &mut a as *mut u8;
    let r = id(unsafe { &mut *p });
    unsafe { *p = 1 };
    *r = 2;
}
