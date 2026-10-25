// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks
//! A reference derived from one pointer of an array is invalidated by a write through a copy of
//! it in another element.

#[kani::proof]
fn ub_shadow_array_ref() {
    let mut a = 1;
    let arr = [&mut a as *mut i32; 2];
    let r = unsafe { &mut *arr[0] };
    unsafe { *arr[1] = 5 };
    *r = 3;
}
