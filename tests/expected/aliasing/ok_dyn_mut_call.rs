// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks
//! Pointer tags pass through calls through `&mut dyn`, in both directions.

trait T {
    fn set(&mut self, v: u8);
    fn me(&mut self) -> &mut u8;
}
struct S {
    v: u8,
}
impl T for S {
    fn set(&mut self, v: u8) {
        self.v = v;
    }
    fn me(&mut self) -> &mut u8 {
        &mut self.v
    }
}

#[kani::proof]
fn ok_dyn_mut_call() {
    let mut s = S { v: 0 };
    let r: &mut dyn T = &mut s;
    r.set(7);
    *r.me() = 3;
    assert!(s.v == 3);
}
