// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

#[kani::proof]
fn ok_reborrow_chain() {
    let mut x = 0;
    let r = &mut x;
    let r2 = &mut *r;
    *r2 = 1;
    *r = 2;
    assert_eq!(x, 2);
}