// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

// After `a` is written, a read through the parent freezes it; writing through it again is UB.
#[kani::proof]
fn ub_frozen_by_foreign_read() {
    let mut x = 0;
    let p = &mut x as *mut i32;
    let a = unsafe { &mut *p };
    *a = 1;
    let _v = unsafe { *p };
    *a = 2;
}
