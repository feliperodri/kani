// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

// A `copy_nonoverlapping` into the memory behind a live `&mut` invalidates it.
#[kani::proof]
fn ub_copy_invalidates_ref() {
    let src = [7u8; 2];
    let mut dst = [0u8; 2];
    let p = &mut dst as *mut [u8; 2] as *mut u8;
    let r = unsafe { &mut *p };
    unsafe { std::ptr::copy_nonoverlapping(src.as_ptr(), p, 2) };
    *r = 1;
}
