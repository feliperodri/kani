// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

// A write through a pointer created from an exposed address disables a sibling of the exposed
// pointer.
#[kani::proof]
fn ub_exposed_write_disables_sibling() {
    let mut x = 0i32;
    let p = &mut x as *mut i32;
    let a = unsafe { &mut *p };
    let b = unsafe { &mut *p };
    let addr = (a as *mut i32).expose_provenance();
    let q = std::ptr::with_exposed_provenance_mut::<i32>(addr);
    unsafe { *q = 1 };
    *b = 2;
}
