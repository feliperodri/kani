// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z aliasing-checks

#[kani::proof]
fn ok_enum_payload() {
    let mut o = Some(5i32);
    if let Some(v) = o.as_mut() {
        *v += 1;
    }
    let r = &mut o;
    *r = None;
    assert!(o.is_none());
}
