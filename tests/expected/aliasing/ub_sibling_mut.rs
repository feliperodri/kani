// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

// Two sibling mutable references; writing through one disables the other.
#[kani::proof]
fn ub_sibling_mut() {
    let mut x = 0;
    let p = &mut x as *mut i32;
    let a = unsafe { &mut *p };
    let b = unsafe { &mut *p };
    *b = 1;
    *a = 2;
}
