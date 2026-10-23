// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

// A shared reference to a `Cell`, then a mutable reborrow of the same parent that writes, then
// the shared reference is used again.
use std::cell::Cell;

#[kani::proof]
fn ok_cell_shared_then_mut() {
    let mut c = Cell::new(0);
    let p = &mut c as *mut Cell<i32>;
    let r = unsafe { &*p };
    let m = unsafe { &mut *p };
    *m.get_mut() = 1;
    r.set(2);
}
