// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

#[kani::proof]
#[kani::unwind(5)]
fn ok_std_iter_mut() {
    let mut a = [1u32, 2, 3, 4];
    for x in a.iter_mut() {
        *x *= 2;
    }
    let s: u32 = a.iter().sum();
    let (l, r) = a.split_at_mut(2);
    l[0] += r[1];
    assert_eq!(s, 20);
    assert_eq!(a[0], 10);
}