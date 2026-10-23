// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

#[kani::proof]
fn ok_split_at_mut() {
    let mut arr = [1u8, 2, 3, 4];
    let (a, b) = arr.split_at_mut(2);
    a[0] = b[1];
    b[0] = a[1];
    assert_eq!(arr, [4, 2, 2, 4]);
}
