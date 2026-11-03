// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

// More references to the same location than Kani tracks at once.
#[kani::proof]
#[kani::unwind(71)]
fn ok_loop_many_borrows() {
    let mut x = 0u32;
    let p = &mut x as *mut u32;
    for _ in 0..70 {
        let r = unsafe { &mut *p };
        *r += 1;
    }
    assert_eq!(x, 70);
}
