// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// RFC 0016 example. Run: kani loops.rs -Z aliasing-checks -Z loop-contracts

#![feature(stmt_expr_attributes)]
#![feature(proc_macro_hygiene)]

/// Each iteration reborrows `r` into `t` and writes through `t`; after the loop, `x` is used
/// directly. No undefined behavior.
#[kani::proof]
fn reborrow_in_loop() {
    let mut x: u32 = 0;
    let r = &mut x;
    let mut i: u32 = 0;
    #[kani::loop_invariant(i <= 3)]
    #[kani::loop_modifies(&i, &*r)]
    while i < 3 {
        let t = &mut *r;
        *t = i;
        i += 1;
    }
    x = 7; // a later, valid use of `x`
    assert!(x == 7);
}

/// The same loop, but iteration 1 also writes `x` through a raw pointer `p` that `r` was
/// derived from, which disables `r`; iteration 2 then writes through a reborrow of `r`. UB.
#[kani::proof]
fn write_through_parent_in_loop() {
    let mut x: u32 = 0;
    let p = &raw mut x;
    let r = unsafe { &mut *p };
    let mut i: u32 = 0;
    #[kani::loop_invariant(i <= 3)]
    #[kani::loop_modifies(&i, p)]
    while i < 3 {
        if i == 1 {
            unsafe { *p = 10 };
        } else {
            let t = &mut *r;
            *t = i; // UB when i == 2: `r` was disabled in iteration 1
        }
        i += 1;
    }
}
