// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

use std::cell::Cell;

#[kani::proof]
fn ok_cell_write_through_aliases() {
    let c = Cell::new(0);
    let p = &c as *const Cell<i32>;
    let r = &c;
    unsafe { (*p).set(1) };
    r.set(r.get() + 1);
    unsafe { (*p).set((*p).get() + 1) };
    assert_eq!(c.get(), 3);
}
