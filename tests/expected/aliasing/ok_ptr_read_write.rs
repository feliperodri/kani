// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

#[kani::proof]
fn ok_ptr_read_write() {
    let mut a = [1u16, 2];
    let p = a.as_mut_ptr();
    unsafe {
        let x = p.read();
        p.add(1).write(x + 5);
        std::ptr::swap(p, p.add(1));
    }
    assert_eq!(a, [6, 1]);
}