// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks
//! A reference returned through a call through `&mut dyn` is invalidated by a write through the
//! pointer the trait object comes from.

trait T {
    fn me(&mut self) -> &mut u8;
}
struct S {
    v: u8,
}
impl T for S {
    fn me(&mut self) -> &mut u8 {
        &mut self.v
    }
}

#[kani::proof]
fn ub_dyn_mut_call() {
    let mut s = S { v: 1 };
    let p = &mut s as *mut S;
    let r: &mut dyn T = unsafe { &mut *p };
    let m: &mut u8 = r.me();
    unsafe { (*p).v = 2 };
    *m = 3;
}
