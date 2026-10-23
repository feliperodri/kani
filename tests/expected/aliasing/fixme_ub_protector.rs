// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

// Writing through an alias of a protected `&mut` argument while the function runs. UB with
// protectors (both models); Kani does not model protectors yet.
#[inline(never)]
fn f(a: &mut i32, p: *mut i32) {
    *a = 1;
    unsafe { *p = 2 };
}

#[kani::proof]
fn ub_protector() {
    let mut x = 0;
    let p = &mut x as *mut i32;
    f(unsafe { &mut *p }, p);
}
