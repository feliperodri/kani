// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

#[kani::proof]
fn ok_disjoint_fields() {
    let mut s = (0u32, 0u32);
    let p = &mut s as *mut (u32, u32);
    let a = unsafe { &mut (*p).0 };
    let b = unsafe { &mut (*p).1 };
    *a = 1;
    *b = 2;
    *a += 1;
    assert_eq!(s, (2, 2));
}
