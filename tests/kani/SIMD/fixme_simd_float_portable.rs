// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Tracking issue: simd_splat not currently supported by Kani after nightly-2026-04-13.

#![feature(portable_simd)]
use std::simd::f32x4;

#[kani::proof]
fn check_sum_portable() {
    let a = f32x4::splat(0.0);
    let b = f32x4::from_array(kani::any());
    kani::assume(b.as_array()[0].is_normal());
    kani::assume(b.as_array()[1].is_normal());
    kani::assume(b.as_array()[2].is_normal());
    kani::assume(b.as_array()[3].is_normal());
    // Cannot compare them directly: https://github.com/model-checking/kani/issues/2632
    assert_eq!((a + b).as_array(), b.as_array());
}
