// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// RFC 0016 examples: a call replaced by its contract (stub_verified).
// kani contracts.rs -Z aliasing-checks -Z function-contracts -Z stubbing

#[kani::requires(true)]
#[kani::modifies(x)]
#[kani::ensures(|_| true)]
fn bump(x: &mut u32) {
    *x = x.wrapping_add(1);
}

#[kani::proof_for_contract(bump)]
fn check_bump() {
    let mut x: u32 = kani::any();
    bump(&mut x);
}

// No UB: the reference passed to the replaced call is used after it.
#[kani::proof]
#[kani::stub_verified(bump)]
fn stub_ok() {
    let mut x: u32 = 0;
    let r = &mut x;
    bump(r);
    *r = 3;
}

// UB: the replaced call writes through a pointer derived from `p`, which disables `r`.
#[kani::proof]
#[kani::stub_verified(bump)]
fn stub_ub_after() {
    let mut x: u32 = 0;
    let p = &mut x as *mut u32;
    let r = unsafe { &mut *p };
    bump(unsafe { &mut *p });
    *r = 2; // UB
}

// UB: a shared reference is disabled by the replaced call's write, then read.
#[kani::proof]
#[kani::stub_verified(bump)]
fn stub_ub_shared() {
    let mut x: u32 = 0;
    let p = &mut x as *mut u32;
    let s = unsafe { &*p };
    bump(unsafe { &mut *p });
    let _v = *s; // UB
}

// UB: the reference passed to the call was disabled before it.
#[kani::proof]
#[kani::stub_verified(bump)]
fn stub_ub_arg() {
    let mut x: u32 = 0;
    let p = &mut x as *mut u32;
    let r = unsafe { &mut *p };
    unsafe { *p = 1 }; // disables `r`
    bump(r); // UB
}

