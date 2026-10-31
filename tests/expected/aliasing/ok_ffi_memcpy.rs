// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks
//! C's `memcpy` and `memcmp` through pointers that may write and read.

extern "C" {
    fn memcpy(d: *mut u8, s: *const u8, n: usize) -> *mut u8;
    fn memcmp(a: *const u8, b: *const u8, n: usize) -> i32;
}

#[kani::proof]
fn ok_ffi_memcpy() {
    let mut x = [0u8; 2];
    let y = [1u8, 2];
    unsafe {
        memcpy(x.as_mut_ptr(), y.as_ptr(), 2);
        assert!(memcmp(x.as_ptr(), y.as_ptr(), 2) == 0);
    }
}
