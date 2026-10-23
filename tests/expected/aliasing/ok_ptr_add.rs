// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

#[kani::proof]
fn ok_ptr_add() {
    let mut a = [0i32; 2];
    let p = &mut a as *mut [i32; 2] as *mut i32;
    let r = unsafe { &mut *p.add(1) };
    *r = 1;
    unsafe { *p.add(1) += 5 };
    assert_eq!(a[1], 6);
}
