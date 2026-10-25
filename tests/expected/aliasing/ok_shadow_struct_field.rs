// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks
//! A reference stored in a struct that is reached through a reference: its tag is kept in shadow
//! memory.

struct Holder<'a> {
    r: &'a mut i32,
    n: u8,
}

fn set(h: &mut Holder) {
    *h.r = 5;
}

#[kani::proof]
fn ok_shadow_struct_field() {
    let mut x = 1;
    let mut h = Holder { r: &mut x, n: 0 };
    set(&mut h);
    h.n = 1;
    assert!(*h.r == 5);
}
