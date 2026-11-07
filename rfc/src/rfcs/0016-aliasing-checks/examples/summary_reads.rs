// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// RFC 0016 example. Run: kani summary_reads.rs -Z aliasing-checks -Z function-contracts -Z stubbing -Z mem-predicates

// Does a call replaced by its contract (stub_verified) model what the callee does to the
// caller's references when it reaches caller memory without going through its arguments?

static mut G: *mut u32 = core::ptr::null_mut();

/// Reads caller memory through a pointer stored in a global. `modifies` only constrains writes.
#[kani::requires(unsafe { kani::mem::can_dereference(G) })]
#[kani::modifies(y)]
fn peek(y: &mut u32) -> u32 {
    *y = 0;
    unsafe { *G }
}

#[kani::proof_for_contract(peek)]
fn check_peek() {
    let mut a: u32 = kani::any();
    unsafe { G = &raw mut a };
    let mut y: u32 = kani::any();
    peek(&mut y);
}

/// Writes caller memory through a pointer stored in a global, which `modifies` names.
#[kani::requires(unsafe { kani::mem::can_write(G) })]
#[kani::modifies(unsafe { G })]
fn poke() {
    unsafe { *G = 5 };
}

#[kani::proof_for_contract(poke)]
fn check_poke() {
    let mut a: u32 = kani::any();
    unsafe { G = &raw mut a };
    poke();
}

/// The real program: the read through `G` (the parent `p` of `r`) is a foreign read for `r`,
/// which is Active, so `r` becomes Frozen and the write through it is UB.
fn peek_caller() {
    let mut x: u32 = 0;
    let p = &raw mut x;
    let r = unsafe { &mut *p };
    *r = 1;
    unsafe { G = p };
    let mut y: u32 = 0;
    let _ = peek(&mut y);
    *r = 2; // UB
}

/// The write through `G` (the parent `p` of `r`) disables `r`.
fn poke_caller() {
    let mut x: u32 = 0;
    let p = &raw mut x;
    let r = unsafe { &mut *p };
    *r = 1;
    unsafe { G = p };
    poke();
    *r = 2; // UB
}

#[kani::proof]
fn peek_real() {
    peek_caller();
}

#[kani::proof]
#[kani::stub_verified(peek)]
fn peek_stubbed() {
    peek_caller();
}

#[kani::proof]
fn poke_real() {
    poke_caller();
}

#[kani::proof]
#[kani::stub_verified(poke)]
fn poke_stubbed() {
    poke_caller();
}

fn main() {
    if std::env::args().count() > 1 { poke_caller() } else { peek_caller() }
}
