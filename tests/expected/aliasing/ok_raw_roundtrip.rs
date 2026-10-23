// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

#[kani::proof]
fn ok_raw_roundtrip() {
    let mut x = 0;
    let r = &mut x;
    let p = r as *mut i32;
    unsafe { *p = 1 };
    let r2 = unsafe { &mut *p };
    *r2 += 1;
    assert_eq!(x, 2);
}