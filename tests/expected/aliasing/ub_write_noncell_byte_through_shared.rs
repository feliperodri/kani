// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

#![allow(invalid_reference_casting)]

// Only the bytes inside the `Cell` may be written through a shared reference.
use std::cell::Cell;

struct S {
    a: Cell<u8>,
    b: u8,
}

#[kani::proof]
fn ub_write_noncell_byte_through_shared() {
    let s = S { a: Cell::new(0), b: 0 };
    let r = &s;
    r.a.set(1);
    let p = &r.b as *const u8 as *mut u8;
    unsafe { *p = 1 };
}
