// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

// Zero-sized accesses never conflict.
#[kani::proof]
fn ok_zst() {
    let mut u = ();
    let p = &mut u as *mut ();
    let r = unsafe { &mut *p };
    unsafe { *p = () };
    *r = ();
}
