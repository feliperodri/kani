// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

// Once the function returns, its argument is no longer protected.
#[inline(never)]
fn f(a: &mut i32) {
    *a = 1;
}

#[kani::proof]
fn ok_protector_ends_on_return() {
    let mut x = 0;
    let p = &mut x as *mut i32;
    f(unsafe { &mut *p });
    unsafe { *p = 2 };
    assert_eq!(x, 2);
}
