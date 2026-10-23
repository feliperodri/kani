// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

#[kani::proof]
fn ok_std_option_as_mut() {
    let mut o = Some(Box::new(1i32));
    if let Some(b) = o.as_mut() {
        **b += 1;
    }
    let r = o.as_deref_mut().unwrap();
    *r += 1;
    let taken = o.take().unwrap();
    assert_eq!(*taken, 3);
}
