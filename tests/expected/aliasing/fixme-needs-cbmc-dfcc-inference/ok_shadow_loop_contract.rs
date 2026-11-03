// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks -Z loop-contracts
//! CBMC havocs what a loop contract assigns, without updating the tags in shadow memory: after
//! the loop, the tag of the reference in the array is unknown, so the access is inconclusive
//! rather than checked against a stale tag.

#![feature(stmt_expr_attributes)]
#![feature(proc_macro_hygiene)]

#[kani::proof]
fn ok_shadow_loop_contract() {
    let mut a = 1;
    let mut b = 2;
    let pb = &mut b as *mut i32;
    let mut slots: [&mut i32; 1] = [&mut a];
    let mut i: u8 = 0;
    #[kani::loop_invariant(i <= 3)]
    while i < 3 {
        slots[0] = unsafe { &mut *pb };
        i += 1;
    }
    *slots[0] = 5;
}
