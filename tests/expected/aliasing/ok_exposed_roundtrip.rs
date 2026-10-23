// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

// A pointer created from an exposed address may be used like the exposed pointer.
#[kani::proof]
fn ok_exposed_roundtrip() {
    let mut x = 0i32;
    let r = &mut x;
    let addr = (r as *mut i32).expose_provenance();
    let p = std::ptr::with_exposed_provenance_mut::<i32>(addr);
    unsafe { *p = 1 };
    assert_eq!(x, 1);
}
