// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

// Mutating the bytes once the `&CStr` is no longer used is fine.
use std::ffi::CStr;

/// `CStr::from_ptr` without the `strlen` call (a foreign function Kani does not model here).
unsafe fn cstr_from_ptr<'a>(p: *const std::ffi::c_char, len_with_nul: usize) -> &'a CStr {
    unsafe {
        CStr::from_bytes_with_nul_unchecked(std::slice::from_raw_parts(p.cast(), len_with_nul))
    }
}

#[kani::proof]
#[kani::unwind(4)]
fn ok_cstr_mutate_after_borrow() {
    let mut buf = [b'a' as std::ffi::c_char, b'b' as std::ffi::c_char, 0];
    let p = buf.as_mut_ptr();
    let s: &CStr = unsafe { cstr_from_ptr(p, 3) };
    assert_eq!(s.to_bytes().len(), 2);
    unsafe { *p = b'z' as std::ffi::c_char };
}
