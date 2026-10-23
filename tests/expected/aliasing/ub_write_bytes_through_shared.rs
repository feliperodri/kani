// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

#![allow(invalid_reference_casting)]

// `write_bytes` through a pointer derived from a shared reference.
#[kani::proof]
fn ub_write_bytes_through_shared() {
    let x = [1u8; 2];
    let s = &x;
    let p = s as *const [u8; 2] as *mut u8;
    unsafe { std::ptr::write_bytes(p, 0, 2) };
}
