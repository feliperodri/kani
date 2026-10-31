// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks
//! Calls through function pointers do not pass pointer tags: the access in the callee is
//! inconclusive.

fn read(x: &u8) -> u8 {
    *x
}

#[kani::proof]
fn ok_fn_pointer_call() {
    let v = 5u8;
    let f: fn(&u8) -> u8 = read;
    assert!(f(&v) == 5);
}
