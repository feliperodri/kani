// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

// A `&mut` argument that was never written sees a foreign read, then is written: UB under Tree
// Borrows' protector rules (reserved, conflicted), and under Stacked Borrows.
#[inline(never)]
fn f(a: &mut i32, p: *const i32) {
    let _v = unsafe { *p };
    *a = 1;
}

#[kani::proof]
fn ub_protector_conflicted() {
    let mut x = 0;
    let p = &mut x as *mut i32;
    f(unsafe { &mut *p }, p);
}
