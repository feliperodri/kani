// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

// The reference to the second element is invalidated by a write through the array pointer.
#[kani::proof]
fn ub_ptr_add() {
    let mut a = [0i32; 2];
    let p = &mut a as *mut [i32; 2] as *mut i32;
    let r = unsafe { &mut *p.add(1) };
    unsafe { *p.add(1) = 5 };
    *r = 1;
}