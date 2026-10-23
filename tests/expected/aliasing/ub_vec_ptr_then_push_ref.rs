// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

// A reference into the vector, then a write through a raw pointer to the same element.
#[kani::proof]
fn ub_vec_ptr_then_push_ref() {
    let mut v = vec![0u8; 2];
    let p = v.as_mut_ptr();
    let r = unsafe { &mut *p };
    unsafe { *p = 1 };
    *r = 2;
}
