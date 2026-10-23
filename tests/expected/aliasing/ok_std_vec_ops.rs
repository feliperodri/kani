// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

#[kani::proof]
#[kani::unwind(5)]
fn ok_std_vec_ops() {
    let mut v = vec![3u8, 1, 2];
    v.swap(0, 2);
    v.retain(|x| *x != 1);
    v.insert(0, 9);
    let last = v.pop();
    v.extend_from_slice(&[7, 7]);
    v.truncate(3);
    assert_eq!(last, Some(3));
    assert_eq!(v, [9, 2, 7]);
}
