// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

// Deallocating memory that a reference argument of a running function points to.
use std::alloc::{Layout, alloc, dealloc};

#[inline(never)]
fn f(_r: &mut u8, p: *mut u8) {
    unsafe { dealloc(p, Layout::new::<u8>()) };
}

#[kani::proof]
fn ub_dealloc_protected() {
    unsafe {
        let p = alloc(Layout::new::<u8>());
        *p = 0;
        f(&mut *p, p);
    }
}
