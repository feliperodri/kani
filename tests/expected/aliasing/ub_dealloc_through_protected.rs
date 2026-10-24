// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

//! Deallocating memory that a reference argument of a running function points to is undefined
//! behavior even through that reference: the write that deallocation performs is local to it, and
//! the reference's strong protector forbids the deallocation itself.

use std::alloc::{Layout, alloc, dealloc};

#[inline(never)]
fn f(r: &mut u8) {
    unsafe { dealloc(r as *mut u8, Layout::new::<u8>()) };
}

#[kani::proof]
fn ub_dealloc_through_protected() {
    unsafe {
        let p = alloc(Layout::new::<u8>());
        *p = 0;
        f(&mut *p);
    }
}
