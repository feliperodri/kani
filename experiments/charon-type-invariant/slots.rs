// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! A container of at most two values of any type `T`.
//!
//! Type invariant (see `Slots.inv` in `SlotsProof.lean` and `is_valid` below):
//! 1. `len` is the number of occupied slots, and
//! 2. slot `b` is occupied only if slot `a` is.
//!
//! The operations only move values (no generic method calls, no drops of `T`): that is the subset
//! the Charon pipeline in this experiment handles (see TODO.md).

pub struct Slots<T> {
    pub a: Option<T>,
    pub b: Option<T>,
    pub len: u8,
}

pub fn new<T>() -> Slots<T> {
    Slots { a: None, b: None, len: 0 }
}

/// Stores `x` in the first free slot. Gives `x` back if both slots are full.
pub fn push<T>(s: Slots<T>, x: T) -> (Slots<T>, Option<T>) {
    let Slots { a, b, len } = s;
    match a {
        None => (Slots { a: Some(x), b, len: len + 1 }, None),
        Some(va) => match b {
            None => (Slots { a: Some(va), b: Some(x), len: len + 1 }, None),
            Some(vb) => (Slots { a: Some(va), b: Some(vb), len }, Some(x)),
        },
    }
}

/// Removes the most recently stored value, if any.
pub fn pop<T>(s: Slots<T>) -> (Slots<T>, Option<T>) {
    let Slots { a, b, len } = s;
    match b {
        Some(vb) => (Slots { a, b: None, len: len - 1 }, Some(vb)),
        None => match a {
            Some(va) => (Slots { a: None, b: None, len: len - 1 }, Some(va)),
            None => (Slots { a: None, b: None, len }, None),
        },
    }
}

/// The type invariant, for the Kani harnesses (the Lean proof states its own).
#[cfg(kani)]
pub fn is_valid<T>(s: &Slots<T>) -> bool {
    let occupied = s.a.is_some() as u8 + s.b.is_some() as u8;
    s.len == occupied && (s.b.is_none() || s.a.is_some())
}

/// Checks, for one monomorphized `T`, what the Lean proof shows for all `T`: `new` establishes
/// the invariant, `push` and `pop` preserve it and never overflow `len` (Kani checks that), and
/// `pop` returns what the last `push` stored.
#[cfg(kani)]
mod verification {
    use super::*;

    fn any_valid<T: kani::Arbitrary>() -> Slots<T> {
        let s = Slots { a: kani::any(), b: kani::any(), len: kani::any() };
        kani::assume(is_valid(&s));
        s
    }

    fn check<T: kani::Arbitrary + PartialEq + Clone>() {
        assert!(is_valid(&new::<T>()));
        let s: Slots<T> = any_valid();
        let x: T = kani::any();
        let was_full = s.b.is_some();
        let (s, rejected) = push(s, x.clone());
        assert!(is_valid(&s));
        assert_eq!(rejected.is_some(), was_full);
        let (s, popped) = pop(s);
        assert!(is_valid(&s));
        if !was_full {
            assert!(popped == Some(x));
        }
    }

    #[kani::proof]
    fn check_u8() {
        check::<u8>();
    }

    #[kani::proof]
    fn check_u64() {
        check::<u64>();
    }

    #[kani::proof]
    fn check_char() {
        check::<char>();
    }

    #[kani::proof]
    fn check_tuple() {
        check::<(u16, bool)>();
    }

    #[kani::proof]
    fn check_array() {
        check::<[i32; 3]>();
    }

    #[kani::proof]
    fn check_option() {
        check::<Option<u32>>();
    }

    /// `String` has no `Arbitrary` impl, so build the slots from a few candidate strings.
    #[kani::proof]
    fn check_string() {
        fn any_string() -> Option<String> {
            match kani::any::<u8>() % 3 {
                0 => None,
                1 => Some(String::from("a")),
                _ => Some(String::from("bc")),
            }
        }
        let s = Slots { a: any_string(), b: any_string(), len: kani::any() };
        kani::assume(is_valid(&s));
        let (s, _) = push(s, String::from("x"));
        assert!(is_valid(&s));
        let (s, _) = pop(s);
        assert!(is_valid(&s));
    }
}
