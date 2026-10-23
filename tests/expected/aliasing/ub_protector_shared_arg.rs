// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

// Writing through an alias of a `&T` argument while the function runs.
#[inline(never)]
fn f(a: &i32, p: *mut i32) -> i32 {
    unsafe { *p = 2 };
    0
}

#[kani::proof]
fn ub_protector_shared_arg() {
    let mut x = 0;
    let p = &mut x as *mut i32;
    let _ = f(unsafe { &*p }, p);
}
