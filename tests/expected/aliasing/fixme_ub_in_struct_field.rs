// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

// The reference is stored in a struct; Kani loses its tag (wildcard) and misses the UB.
struct Holder<'a> {
    r: &'a mut i32,
}

#[kani::proof]
fn ub_in_struct_field() {
    let mut x = 0;
    let p = &mut x as *mut i32;
    let h = Holder { r: unsafe { &mut *p } };
    unsafe { *p = 1 };
    *h.r = 2;
}