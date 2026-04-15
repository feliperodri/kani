// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

// The generic `fabs` intrinsic is not yet supported for f16/f128 types.
// These harnesses fail because `is_finite()` calls `abs()` which calls `fabs`.
#![feature(core_intrinsics)]
#![feature(f16)]
#![feature(f128)]

use std::intrinsics::float_to_int_unchecked;

macro_rules! check_float_to_int_unchecked_no_assert {
    ($float_ty:ty, $int_ty:ty) => {
        let f: $float_ty = kani::any_where(|f: &$float_ty| {
            f.is_finite() && *f > <$int_ty>::MIN as $float_ty && *f < <$int_ty>::MAX as $float_ty
        });
        let _u: $int_ty = unsafe { float_to_int_unchecked(f) };
    };
}

#[kani::proof]
fn check_f16_to_int_unchecked() {
    check_float_to_int_unchecked_no_assert!(f16, u8);
    check_float_to_int_unchecked_no_assert!(f16, u16);
    check_float_to_int_unchecked_no_assert!(f16, u32);
    check_float_to_int_unchecked_no_assert!(f16, u64);
    check_float_to_int_unchecked_no_assert!(f16, u128);
    check_float_to_int_unchecked_no_assert!(f16, usize);
    check_float_to_int_unchecked_no_assert!(f16, i8);
    check_float_to_int_unchecked_no_assert!(f16, i16);
    check_float_to_int_unchecked_no_assert!(f16, i32);
    check_float_to_int_unchecked_no_assert!(f16, i64);
    check_float_to_int_unchecked_no_assert!(f16, i128);
    check_float_to_int_unchecked_no_assert!(f16, isize);
}

#[kani::proof]
fn check_f128_to_int_unchecked() {
    check_float_to_int_unchecked_no_assert!(f128, u8);
    check_float_to_int_unchecked_no_assert!(f128, u16);
    check_float_to_int_unchecked_no_assert!(f128, u32);
    check_float_to_int_unchecked_no_assert!(f128, u64);
    check_float_to_int_unchecked_no_assert!(f128, u128);
    check_float_to_int_unchecked_no_assert!(f128, usize);
    check_float_to_int_unchecked_no_assert!(f128, i8);
    check_float_to_int_unchecked_no_assert!(f128, i16);
    check_float_to_int_unchecked_no_assert!(f128, i32);
    check_float_to_int_unchecked_no_assert!(f128, i64);
    check_float_to_int_unchecked_no_assert!(f128, i128);
    check_float_to_int_unchecked_no_assert!(f128, isize);
}
