// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks
//! A shared reference to a `dyn` value: which of its bytes are in an `UnsafeCell` depends on the
//! concrete type, which the checks do not know, so the access is inconclusive. Tracking the
//! concrete type would make this checkable.

trait T {
    fn get(&self) -> u8;
}
struct S {
    v: u8,
}
impl T for S {
    fn get(&self) -> u8 {
        self.v
    }
}

#[kani::proof]
fn ok_dyn_shared_call() {
    let s = S { v: 4 };
    let r: &dyn T = &s;
    assert!(r.get() == 4);
}
