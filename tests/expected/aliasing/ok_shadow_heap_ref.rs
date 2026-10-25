// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks
//! A reference stored on the heap keeps its tag.

#[kani::proof]
fn ok_shadow_heap_ref() {
    let mut x = 0;
    let b: Box<&mut i32> = Box::new(&mut x);
    let p: *mut &mut i32 = Box::into_raw(b);
    unsafe {
        **p = 4;
        drop(Box::from_raw(p));
    }
    assert!(x == 4);
}
