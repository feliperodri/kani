// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks -Z function-contracts
//! The closures that check a contract read the arguments through the references they capture.

#[kani::requires(*x < 100)]
#[kani::ensures(|r| *r == *x)]
#[kani::modifies(x)]
fn bump(x: &mut u32) -> u32 {
    *x += 1;
    let r = &*x;
    *r
}

#[kani::proof_for_contract(bump)]
fn check_bump() {
    let mut v: u32 = kani::any();
    bump(&mut v);
}
