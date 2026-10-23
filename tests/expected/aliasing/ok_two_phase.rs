// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

#[kani::proof]
fn ok_two_phase() {
    let mut v = Vec::with_capacity(2);
    v.push(1usize);
    v.push(v.len());
    assert_eq!(v[1], 1);
}