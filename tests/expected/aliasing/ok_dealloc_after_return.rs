// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

use std::alloc::{Layout, alloc, dealloc};

#[inline(never)]
fn f(r: &mut u8) {
    *r = 1;
}

#[kani::proof]
fn ok_dealloc_after_return() {
    unsafe {
        let p = alloc(Layout::new::<u8>());
        *p = 0;
        f(&mut *p);
        dealloc(p, Layout::new::<u8>());
    }
}
