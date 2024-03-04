// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Zfunction-contracts

//! Check that is possible to use `modifies` clause for verifciation, but not stubbing.
//! Using contracts as stubs require users to ensure the type of the returning experession
//! implements `kani::Arbitrary`. This requirement is not necessary if the contract is
//! only used for verification.

#[kani::requires(*ptr < 100)]
#[kani::modifies(ptr)]
fn modify(ptr: &mut u32) -> &'static str {
    *ptr += 1;
    let msg: &'static str = "done";
    msg
}

#[kani::proof_for_contract(modify)]
fn main() {
    let mut i = kani::any();
    modify(&mut i);
}
