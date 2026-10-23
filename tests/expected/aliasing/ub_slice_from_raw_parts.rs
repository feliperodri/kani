// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

#[kani::proof]
fn ub_slice_from_raw_parts() {
    let mut a = [0u8; 4];
    let p = a.as_mut_ptr();
    let s = unsafe { std::slice::from_raw_parts_mut(p, 4) };
    let first = &mut s[0];
    unsafe { *p = 7 };
    *first = 1;
}