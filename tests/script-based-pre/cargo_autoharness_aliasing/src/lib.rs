// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Automatic harnesses with `-Z aliasing-checks`.

/// Stores a pointer in memory, which writes its tag to shadow memory.
pub fn put<'a>(slot: &mut &'a u32, x: &'a u32) {
    *slot = x;
}

/// Tree Borrows undefined behavior: the write through `r` disables `p`.
pub fn invalidated(x: &mut u32) -> u32 {
    let p = x as *mut u32;
    let r = &mut *x;
    *r = 1;
    unsafe { *p = 2 };
    *r
}

/// The same accesses in an order that keeps both pointers valid.
pub fn valid(x: &mut u32) -> u32 {
    let r = &mut *x;
    *r = 1;
    let p = x as *mut u32;
    unsafe { *p = 2 };
    *x
}
