// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

use std::collections::VecDeque;

#[kani::proof]
#[kani::unwind(6)]
fn ok_std_vecdeque() {
    let mut d: VecDeque<u8> = VecDeque::with_capacity(4);
    d.push_back(1);
    d.push_back(2);
    d.push_front(0);
    d.pop_back();
    d.push_back(3);
    d.push_back(4);
    let (a, b) = d.as_mut_slices();
    if let Some(x) = a.first_mut() {
        *x = 9;
    }
    let _ = b.len();
    assert_eq!(d.front(), Some(&9));
}
