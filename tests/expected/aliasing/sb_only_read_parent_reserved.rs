// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

// UB under Stacked Borrows (the read through `p` pops `a`), fine under Tree Borrows (`a` is
// still reserved: it was never written).
#[kani::proof]
fn sb_only_read_parent_reserved() {
    let mut x = 0;
    let p = &mut x as *mut i32;
    let a = unsafe { &mut *p };
    let _v = unsafe { *p };
    *a = 1;
}