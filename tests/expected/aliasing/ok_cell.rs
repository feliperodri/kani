// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

use std::cell::Cell;

#[kani::proof]
fn ok_cell() {
    let c = Cell::new(0);
    let a = &c;
    let b = &c;
    a.set(1);
    b.set(b.get() + 1);
    assert_eq!(c.get(), 2);
}
