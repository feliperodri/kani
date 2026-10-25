// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks
//! A reference stored on the heap is invalidated by a write through the pointer it comes from.

#[kani::proof]
fn ub_shadow_heap_ref() {
    let mut x = 0;
    let px = &mut x as *mut i32;
    let p: *mut &mut i32 = Box::into_raw(Box::new(unsafe { &mut *px }));
    unsafe {
        *px = 1;
        **p = 4;
        drop(Box::from_raw(p));
    }
}
