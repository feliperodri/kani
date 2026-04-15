// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

// Check that `f32::max` returns the maximum of two values, except in the
// following cases:
//  * If one of the arguments is NaN, the other arguments is returned.
//  * If both arguments are NaN, NaN is returned.

#[kani::proof]
fn test_general() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    kani::assume(!x.is_nan() && !y.is_nan());
    let res = x.max(y);
    if x > y {
        assert!(res == x);
    } else {
        assert!(res == y);
    }
}

#[kani::proof]
fn test_one_nan() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    kani::assume((x.is_nan() && !y.is_nan()) || (!x.is_nan() && y.is_nan()));
    let res = x.max(y);
    if x.is_nan() {
        assert!(res == y);
    } else {
        assert!(res == x);
    }
}

#[kani::proof]
fn test_both_nan() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    kani::assume(x.is_nan() && y.is_nan());
    let res = x.max(y);
    assert!(res.is_nan());
}
