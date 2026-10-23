// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

// The only exposed pointer was derived from `r`, which a later write through the parent disabled.
#[kani::proof]
fn ub_exposed_after_invalidation() {
    let mut x = 0i32;
    let p = &mut x as *mut i32;
    let r = unsafe { &mut *p };
    let addr = (r as *mut i32).expose_provenance();
    unsafe { *p = 1 };
    let q = std::ptr::with_exposed_provenance_mut::<i32>(addr);
    unsafe { *q = 2 };
}
