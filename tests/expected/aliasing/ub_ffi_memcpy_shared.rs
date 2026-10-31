// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks
//! C's `memcpy` writing through a pointer derived from a shared reference.

extern "C" {
    fn memcpy(d: *mut u8, s: *const u8, n: usize) -> *mut u8;
}

#[kani::proof]
fn ub_ffi_memcpy_shared() {
    let x = 0u8;
    let y = 1u8;
    let p = &x as *const u8 as *mut u8;
    unsafe { memcpy(p, &y, 1) };
}
