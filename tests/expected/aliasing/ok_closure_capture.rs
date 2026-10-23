// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

#[kani::proof]
fn ok_closure_capture() {
    let mut count = 0;
    let mut inc = || count += 1;
    inc();
    inc();
    let r = &count;
    assert_eq!(*r, 2);
}