// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

#[kani::proof]
fn ub_read_after_invalidation() {
    let mut x = 0;
    let p = &mut x as *mut i32;
    let r = unsafe { &mut *p };
    unsafe { *p = 1 };
    let _v = *r;
}