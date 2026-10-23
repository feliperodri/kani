// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

use std::cell::RefCell;
use std::rc::Rc;

#[kani::proof]
fn ok_std_refcell_rc() {
    let shared = Rc::new(RefCell::new(vec![1u8]));
    let other = Rc::clone(&shared);
    other.borrow_mut().push(2);
    {
        let b = shared.borrow();
        assert_eq!(b.len(), 2);
    }
    shared.borrow_mut()[0] = 5;
    assert_eq!(other.borrow()[0], 5);
}