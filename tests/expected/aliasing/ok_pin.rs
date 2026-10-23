// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

use std::pin::Pin;

#[kani::proof]
fn ok_pin() {
    let mut x = 1u32;
    let mut pinned = Pin::new(&mut x);
    *pinned.as_mut().get_mut() += 1;
    let r = Pin::into_inner(pinned);
    *r += 1;
    assert_eq!(x, 3);
}
