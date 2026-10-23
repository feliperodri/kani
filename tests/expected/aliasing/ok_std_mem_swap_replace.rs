// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

#[kani::proof]
fn ok_std_mem_swap_replace() {
    let mut a = String::from("a");
    let mut b = String::from("bb");
    std::mem::swap(&mut a, &mut b);
    let old = std::mem::replace(&mut a, String::new());
    let t = std::mem::take(&mut b);
    assert_eq!(old.len(), 2);
    assert_eq!(t.len(), 1);
}
