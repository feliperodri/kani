// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

#[kani::proof]
fn ok_copy_then_ref() {
    let src = [7u8; 2];
    let mut dst = [0u8; 2];
    let p = &mut dst as *mut [u8; 2] as *mut u8;
    unsafe { std::ptr::copy_nonoverlapping(src.as_ptr(), p, 2) };
    let r = unsafe { &mut *p };
    *r += 1;
    assert_eq!(dst, [8, 7]);
}
