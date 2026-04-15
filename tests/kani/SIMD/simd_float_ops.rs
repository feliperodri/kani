// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Ensure we can handle SIMD defined in the standard library
#![allow(non_camel_case_types)]
#![feature(repr_simd, core_intrinsics)]
use std::intrinsics::simd::simd_add;

#[repr(simd)]
#[derive(Copy, Clone, kani::Arbitrary)]
pub struct f32x2([f32; 2]);

impl f32x2 {
    fn as_array(&self) -> &[f32; 2] {
        unsafe { &*(self as *const f32x2 as *const [f32; 2]) }
    }
}

#[kani::proof]
fn check_sum() {
    let a = f32x2([0.0, 0.0]);
    let b = kani::any::<f32x2>();
    kani::assume(b.as_array()[0].is_normal());
    kani::assume(b.as_array()[1].is_normal());
    let sum = unsafe { simd_add(a, b) };
    assert_eq!(sum.as_array(), b.as_array());
}
