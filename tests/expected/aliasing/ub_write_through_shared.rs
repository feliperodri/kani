// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

#![allow(invalid_reference_casting)]

#[kani::proof]
fn ub_write_through_shared() {
    let x = 0;
    let r = &x;
    let p = r as *const i32 as *mut i32;
    unsafe { *p = 1 };
}