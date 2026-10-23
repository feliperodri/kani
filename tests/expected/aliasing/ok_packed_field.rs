// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

#[repr(C, packed)]
struct P {
    a: u8,
    b: u32,
}

#[kani::proof]
fn ok_packed_field() {
    let mut s = P { a: 0, b: 0 };
    let r = unsafe { &mut *(&raw mut s.a) };
    unsafe { (&raw mut s.b).write_unaligned(7) };
    *r = 2;
    let b = unsafe { (&raw const s.b).read_unaligned() };
    assert_eq!(b, 7);
}
