// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

// A reference into an enum's payload is invalidated by overwriting the enum.
#[kani::proof]
fn ub_enum_payload() {
    let mut o = Some(5i32);
    let p = &mut o as *mut Option<i32>;
    let r = match unsafe { &mut *p } {
        Some(v) => v,
        None => return,
    };
    unsafe { *p = Some(6) };
    *r = 1;
}
