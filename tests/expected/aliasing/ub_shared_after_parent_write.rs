// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

#[kani::proof]
fn ub_shared_after_parent_write() {
    let mut x = 0;
    let p = &mut x as *mut i32;
    let s = unsafe { &*p };
    unsafe { *p = 1 };
    let _v = *s;
}
