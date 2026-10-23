// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

// The returned reference is the argument's; the parent's write disables it.
#[inline(never)]
fn id(r: &mut i32) -> &mut i32 {
    r
}

#[kani::proof]
fn ub_across_call() {
    let mut x = 0;
    let p = &mut x as *mut i32;
    let r = id(unsafe { &mut *p });
    unsafe { *p = 1 };
    *r = 2;
}