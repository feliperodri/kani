// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

#[kani::proof]
fn ok_shared_readers() {
    let mut x = 1;
    let p = &mut x as *mut i32;
    let a = unsafe { &*p };
    let b = unsafe { &*p };
    assert_eq!(*a + *b, 2);
    unsafe { *p = 3 };
    assert_eq!(x, 3);
}
