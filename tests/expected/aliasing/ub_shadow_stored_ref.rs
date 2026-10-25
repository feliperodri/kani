// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks
//! A reference stored through a raw pointer is invalidated by a write through a sibling.

#[kani::proof]
fn ub_shadow_stored_ref() {
    let mut x = 1;
    let mut slot: Option<&mut i32> = None;
    let p = &mut slot as *mut Option<&mut i32>;
    unsafe {
        *p = Some(&mut *(&mut x as *mut i32));
        let raw = &mut x as *mut i32;
        *raw = 2;
        if let Some(r) = &mut *p {
            **r = 3;
        }
    }
}
