// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks
//! C's `memset` writing through a pointer derived from a shared reference. Found by an external
//! soundness audit: foreign calls used to be unchecked, and this verified.

extern "C" {
    fn memset(p: *mut u8, c: i32, n: usize) -> *mut u8;
}

#[kani::proof]
fn ub_ffi_memset_shared() {
    let x = 0u8;
    let p = &x as *const u8 as *mut u8;
    unsafe { memset(p, 1, 1) };
}
