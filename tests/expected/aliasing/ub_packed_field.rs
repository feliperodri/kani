// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

// A raw write to a packed field invalidates a reference to it.
#[repr(C, packed)]
struct P {
    a: u8,
    b: u32,
}

#[kani::proof]
fn ub_packed_field() {
    let mut s = P { a: 0, b: 0 };
    let r = unsafe { &mut *(&raw mut s.a) };
    unsafe { (&raw mut s.b).write_unaligned(7) };
    unsafe { (&raw mut s.a).write(1) };
    *r = 2;
}
