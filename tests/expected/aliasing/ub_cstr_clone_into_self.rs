// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

#![feature(clone_to_uninit)]

// verify-rust-std#733, obligation 2: `clone_to_uninit` with a `dest` that overlaps `self`.
use std::clone::CloneToUninit;
use std::ffi::CStr;

/// `CStr::from_ptr` without the `strlen` call (a foreign function Kani does not model here).
unsafe fn cstr_from_ptr<'a>(p: *const std::ffi::c_char, len_with_nul: usize) -> &'a CStr {
    unsafe {
        CStr::from_bytes_with_nul_unchecked(std::slice::from_raw_parts(p.cast(), len_with_nul))
    }
}

#[kani::proof]
#[kani::unwind(6)]
fn ub_cstr_clone_into_self() {
    let mut buf = [b'a' as std::ffi::c_char, b'b' as std::ffi::c_char, 0, 0];
    let p = buf.as_mut_ptr();
    let s: &CStr = unsafe { cstr_from_ptr(p, 3) };
    unsafe { s.clone_to_uninit(p.add(1) as *mut u8) };
}
