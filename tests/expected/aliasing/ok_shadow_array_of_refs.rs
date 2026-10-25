// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks
//! References in an array, indexed with a non-deterministic index.

#[kani::proof]
fn ok_shadow_array_of_refs() {
    let mut a = 1;
    let mut b = 2;
    let mut arr = [&mut a, &mut b];
    let i: usize = kani::any();
    kani::assume(i < 2);
    *arr[i] += 1;
    assert!(*arr[0] + *arr[1] == 4);
}
