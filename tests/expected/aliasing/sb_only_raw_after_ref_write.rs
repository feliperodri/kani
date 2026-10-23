// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

// UB under Stacked Borrows (the write through `r` pops the raw pointer), fine under Tree Borrows
// (the raw pointer has `r`'s tag).
#[kani::proof]
fn sb_only_raw_after_ref_write() {
    let mut x = 0;
    let r = &mut x;
    let p = r as *mut i32;
    *r = 1;
    unsafe { *p = 2 };
}
