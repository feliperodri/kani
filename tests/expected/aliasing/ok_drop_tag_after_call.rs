// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks
//! References created only to be passed to a call are dropped when it returns, so that program
//! paths that made different calls end with the same tags.

fn read(x: &u8, y: &u8) -> u8 {
    *x + *y
}

#[kani::proof]
fn ok_drop_tag_after_call() {
    let a = 1u8;
    let b = 2u8;
    let c: bool = kani::any();
    let s = if c { read(&a, &b) } else { 3 };
    assert!(s == 3);
    let r = &a;
    assert!(*r == 1);
}
