// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

#[kani::proof]
fn ub_box_write() {
    let mut b = Box::new(0);
    let r = unsafe { &mut *(&mut *b as *mut i32) };
    *b = 1;
    *r = 2;
}