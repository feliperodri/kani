// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

#[inline(never)]
fn add(a: &mut i32, b: &i32) {
    *a += *b;
}

#[kani::proof]
fn ok_call_with_alias_args() {
    let mut x = 1;
    let y = 2;
    add(&mut x, &y);
    let r = &mut x;
    add(r, &y);
    assert_eq!(x, 5);
}
