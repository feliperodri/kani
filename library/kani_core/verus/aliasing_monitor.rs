// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Verus proof that the transition core of Kani's aliasing checks implements the rules it
//! documents.
//!
//! This crate verifies the code Kani runs: it includes `../src/aliasing_monitor.rs` and expands
//! `kani_aliasing_monitor!`, whose functions carry `verus_spec` attributes that only exist when
//! Verus compiles them. This file adds the specification those attributes refer to: an abstract
//! Tree Borrows state at the tracked memory location (a tree of tags, each with a permission),
//! the abstraction function from the monitor's bit sets to it, and the lemmas the proofs use.
//!
//! Run: `verus library/kani_core/verus/aliasing_monitor.rs` (see README.md).

#![allow(unused_imports)]

use vstd::prelude::*;

include!("../src/aliasing_monitor.rs");
kani_aliasing_monitor!();

verus! {

// ---------------------------------------------------------------------------------------------
// Bits
// ---------------------------------------------------------------------------------------------

/// Bit `i` of `m`.
pub open spec fn bit(m: u64, i: u64) -> bool {
    (m >> i) & 1u64 == 1u64
}

pub proof fn lemma_bit_and(a: u64, b: u64, i: u64)
    requires i < 64,
    ensures bit(a & b, i) == (bit(a, i) && bit(b, i)),
{
    assert(((a & b) >> i) & 1u64 == 1u64 <==> ((a >> i) & 1u64 == 1u64 && (b >> i) & 1u64 == 1u64))
        by (bit_vector) requires i < 64;
}

pub proof fn lemma_bit_or(a: u64, b: u64, i: u64)
    requires i < 64,
    ensures bit(a | b, i) == (bit(a, i) || bit(b, i)),
{
    assert(((a | b) >> i) & 1u64 == 1u64 <==> ((a >> i) & 1u64 == 1u64 || (b >> i) & 1u64 == 1u64))
        by (bit_vector) requires i < 64;
}

pub proof fn lemma_bit_not(a: u64, i: u64)
    requires i < 64,
    ensures bit(!a, i) == !bit(a, i),
{
    assert(((!a) >> i) & 1u64 == 1u64 <==> !((a >> i) & 1u64 == 1u64)) by (bit_vector)
        requires i < 64;
}

pub proof fn lemma_bit_single(t: u64, i: u64)
    requires t < 64, i < 64,
    ensures bit(1u64 << t, i) == (i == t),
{
    assert(((1u64 << t) >> i) & 1u64 == 1u64 <==> i == t) by (bit_vector) requires t < 64, i < 64;
}

pub proof fn lemma_bit_below(c: u64, i: u64)
    requires 0 < c < 64, i < 64,
    ensures bit(((1u64 << c) - 1u64) as u64, i) == (i < c),
{
    assert(((((1u64 << c) - 1u64) as u64) >> i) & 1u64 == 1u64 <==> i < c) by (bit_vector)
        requires 0 < c < 64, i < 64;
}

pub proof fn lemma_bit_zero(i: u64)
    requires i < 64,
    ensures !bit(0u64, i),
{
    assert(!((0u64 >> i) & 1u64 == 1u64)) by (bit_vector) requires i < 64;
}

pub proof fn lemma_bit_one(i: u64)
    requires i < 64,
    ensures bit(1u64, i) == (i == 0),
{
    assert(((1u64 >> i) & 1u64 == 1u64) <==> i == 0) by (bit_vector) requires i < 64;
}

// ---------------------------------------------------------------------------------------------
// Masks as sets of tags
// ---------------------------------------------------------------------------------------------

pub proof fn lemma_all_bits_clear(m: u64)
    requires forall|i: u64| i < 64 ==> !bit(m, i),
    ensures m == 0,
{
    assert(!bit(m, 0u64));
    assert(!bit(m, 1u64));
    assert(!bit(m, 2u64));
    assert(!bit(m, 3u64));
    assert(!bit(m, 4u64));
    assert(!bit(m, 5u64));
    assert(!bit(m, 6u64));
    assert(!bit(m, 7u64));
    assert(!bit(m, 8u64));
    assert(!bit(m, 9u64));
    assert(!bit(m, 10u64));
    assert(!bit(m, 11u64));
    assert(!bit(m, 12u64));
    assert(!bit(m, 13u64));
    assert(!bit(m, 14u64));
    assert(!bit(m, 15u64));
    assert(!bit(m, 16u64));
    assert(!bit(m, 17u64));
    assert(!bit(m, 18u64));
    assert(!bit(m, 19u64));
    assert(!bit(m, 20u64));
    assert(!bit(m, 21u64));
    assert(!bit(m, 22u64));
    assert(!bit(m, 23u64));
    assert(!bit(m, 24u64));
    assert(!bit(m, 25u64));
    assert(!bit(m, 26u64));
    assert(!bit(m, 27u64));
    assert(!bit(m, 28u64));
    assert(!bit(m, 29u64));
    assert(!bit(m, 30u64));
    assert(!bit(m, 31u64));
    assert(!bit(m, 32u64));
    assert(!bit(m, 33u64));
    assert(!bit(m, 34u64));
    assert(!bit(m, 35u64));
    assert(!bit(m, 36u64));
    assert(!bit(m, 37u64));
    assert(!bit(m, 38u64));
    assert(!bit(m, 39u64));
    assert(!bit(m, 40u64));
    assert(!bit(m, 41u64));
    assert(!bit(m, 42u64));
    assert(!bit(m, 43u64));
    assert(!bit(m, 44u64));
    assert(!bit(m, 45u64));
    assert(!bit(m, 46u64));
    assert(!bit(m, 47u64));
    assert(!bit(m, 48u64));
    assert(!bit(m, 49u64));
    assert(!bit(m, 50u64));
    assert(!bit(m, 51u64));
    assert(!bit(m, 52u64));
    assert(!bit(m, 53u64));
    assert(!bit(m, 54u64));
    assert(!bit(m, 55u64));
    assert(!bit(m, 56u64));
    assert(!bit(m, 57u64));
    assert(!bit(m, 58u64));
    assert(!bit(m, 59u64));
    assert(!bit(m, 60u64));
    assert(!bit(m, 61u64));
    assert(!bit(m, 62u64));
    assert(!bit(m, 63u64));
    assert(((m >> 0u64) & 1u64 != 1u64 && (m >> 1u64) & 1u64 != 1u64 && (m >> 2u64) & 1u64 != 1u64 && (m >> 3u64) & 1u64 != 1u64 && (m >> 4u64) & 1u64 != 1u64 && (m >> 5u64) & 1u64 != 1u64 && (m >> 6u64) & 1u64 != 1u64 && (m >> 7u64) & 1u64 != 1u64 && (m >> 8u64) & 1u64 != 1u64 && (m >> 9u64) & 1u64 != 1u64 && (m >> 10u64) & 1u64 != 1u64 && (m >> 11u64) & 1u64 != 1u64 && (m >> 12u64) & 1u64 != 1u64 && (m >> 13u64) & 1u64 != 1u64 && (m >> 14u64) & 1u64 != 1u64 && (m >> 15u64) & 1u64 != 1u64 && (m >> 16u64) & 1u64 != 1u64 && (m >> 17u64) & 1u64 != 1u64 && (m >> 18u64) & 1u64 != 1u64 && (m >> 19u64) & 1u64 != 1u64 && (m >> 20u64) & 1u64 != 1u64 && (m >> 21u64) & 1u64 != 1u64 && (m >> 22u64) & 1u64 != 1u64 && (m >> 23u64) & 1u64 != 1u64 && (m >> 24u64) & 1u64 != 1u64 && (m >> 25u64) & 1u64 != 1u64 && (m >> 26u64) & 1u64 != 1u64 && (m >> 27u64) & 1u64 != 1u64 && (m >> 28u64) & 1u64 != 1u64 && (m >> 29u64) & 1u64 != 1u64 && (m >> 30u64) & 1u64 != 1u64 && (m >> 31u64) & 1u64 != 1u64 && (m >> 32u64) & 1u64 != 1u64 && (m >> 33u64) & 1u64 != 1u64 && (m >> 34u64) & 1u64 != 1u64 && (m >> 35u64) & 1u64 != 1u64 && (m >> 36u64) & 1u64 != 1u64 && (m >> 37u64) & 1u64 != 1u64 && (m >> 38u64) & 1u64 != 1u64 && (m >> 39u64) & 1u64 != 1u64 && (m >> 40u64) & 1u64 != 1u64 && (m >> 41u64) & 1u64 != 1u64 && (m >> 42u64) & 1u64 != 1u64 && (m >> 43u64) & 1u64 != 1u64 && (m >> 44u64) & 1u64 != 1u64 && (m >> 45u64) & 1u64 != 1u64 && (m >> 46u64) & 1u64 != 1u64 && (m >> 47u64) & 1u64 != 1u64 && (m >> 48u64) & 1u64 != 1u64 && (m >> 49u64) & 1u64 != 1u64 && (m >> 50u64) & 1u64 != 1u64 && (m >> 51u64) & 1u64 != 1u64 && (m >> 52u64) & 1u64 != 1u64 && (m >> 53u64) & 1u64 != 1u64 && (m >> 54u64) & 1u64 != 1u64 && (m >> 55u64) & 1u64 != 1u64 && (m >> 56u64) & 1u64 != 1u64 && (m >> 57u64) & 1u64 != 1u64 && (m >> 58u64) & 1u64 != 1u64 && (m >> 59u64) & 1u64 != 1u64 && (m >> 60u64) & 1u64 != 1u64 && (m >> 61u64) & 1u64 != 1u64 && (m >> 62u64) & 1u64 != 1u64 && (m >> 63u64) & 1u64 != 1u64) ==> m == 0u64) by (bit_vector);
}

/// A non-zero mask has a set bit.
pub proof fn lemma_nonzero_witness(m: u64)
    requires m != 0,
    ensures exists|i: u64| i < 64 && bit(m, i),
{
    if forall|i: u64| i < 64 ==> !bit(m, i) {
        lemma_all_bits_clear(m);
    }
}

/// `x & y` is non-zero exactly when some bit is set in both.
pub proof fn lemma_and_nonzero(x: u64, y: u64)
    ensures (x & y != 0) == exists|i: u64| i < 64 && bit(x, i) && bit(y, i),
{
    if x & y != 0 {
        lemma_nonzero_witness(x & y);
        let i = choose|i: u64| i < 64 && bit(x & y, i);
        lemma_bit_and(x, y, i);
    } else {
        assert forall|i: u64| i < 64 implies !(bit(x, i) && bit(y, i)) by {
            lemma_bit_and(x, y, i);
            lemma_bit_zero(i);
        }
    }
}

/// `v & l == l` exactly when every bit of `l` is set in `v`.
pub proof fn lemma_subset(v: u64, l: u64)
    ensures (v & l == l) == forall|i: u64| i < 64 && bit(l, i) ==> bit(v, i),
{
    assert((v & l == l) <==> (l & !v == 0u64)) by (bit_vector);
    lemma_and_nonzero(l, !v);
    if l & !v != 0 {
        let i = choose|i: u64| i < 64 && bit(l, i) && bit(!v, i);
        lemma_bit_not(v, i);
    } else {
        assert forall|i: u64| i < 64 && bit(l, i) implies bit(v, i) by {
            lemma_bit_not(v, i);
        }
    }
}

// ---------------------------------------------------------------------------------------------
// Abstract state: Tree Borrows at the tracked location
// ---------------------------------------------------------------------------------------------

/// Tree Borrows' permissions (Villani et al., PLDI 2025, Fig. 3), with the two variants of
/// Reserved: conflicted (a protected tag that saw a foreign read) and interior-mutable.
pub enum Perm {
    Reserved { conflicted: bool, interior: bool },
    Active,
    Frozen,
    Disabled,
}

pub struct Node {
    /// The tag's ancestors, including itself.
    pub ancestors: ISet<nat>,
    pub perm: Perm,
    pub protected: bool,
    pub initialized: bool,
    /// A shared reference to the bytes of an `UnsafeCell`: not a node of the tree at this
    /// location; accesses through it are accesses through `alias`.
    pub cell: bool,
    pub alias: nat,
    pub exposed: bool,
}

pub struct AbsState {
    pub count: nat,
    pub nodes: IMap<nat, Node>,
    /// A pointer whose tag is unknown was exposed.
    pub unknown_exposed: bool,
}

pub open spec fn perm_of(s: &MonitorState, t: u64) -> Perm {
    if !bit(s.valid, t) {
        Perm::Disabled
    } else if bit(s.frozen, t) {
        Perm::Frozen
    } else if bit(s.active, t) {
        Perm::Active
    } else {
        Perm::Reserved { conflicted: bit(s.conflicted, t), interior: bit(s.interior, t) }
    }
}

pub open spec fn mask_set(m: u64) -> ISet<nat> {
    ISet::new(|i: nat| i < 64 && bit(m, i as u64))
}

pub open spec fn node_of(s: &MonitorState, t: u64) -> Node {
    Node {
        ancestors: mask_set(s.ancestors[t as int]),
        perm: perm_of(s, t),
        protected: bit(s.protected, t),
        initialized: bit(s.initialized, t),
        cell: bit(s.cell, t),
        alias: s.alias[t as int] as nat,
        exposed: bit(s.exposed, t),
    }
}

/// The abstraction function: the tags `0..count` and their nodes.
pub open spec fn abstraction(s: &MonitorState) -> AbsState {
    AbsState {
        count: s.count as nat,
        nodes: IMap::new(|t: nat| t < s.count as nat, |t: nat| node_of(s, t as u64)),
        unknown_exposed: s.unknown_exposed,
    }
}

/// The state after `monitor_initialize`: one root tag, Active and initialized.
pub open spec fn initial_spec(a: AbsState) -> bool {
    &&& a.count == 1
    &&& forall|t: nat| a.nodes.dom().contains(t) <==> t == 0
    &&& forall|u: nat| a.nodes[0].ancestors.contains(u) <==> u == 0
    &&& a.nodes[0].perm == Perm::Active
    &&& !a.nodes[0].protected
    &&& a.nodes[0].initialized
    &&& !a.nodes[0].cell
    &&& !a.nodes[0].exposed
    &&& !a.unknown_exposed
}

// ---------------------------------------------------------------------------------------------
// Well-formedness of the monitor state (Stage 0-1: tags and ancestry)
// ---------------------------------------------------------------------------------------------

/// Every bit set has no bit at or above `count`.
pub open spec fn clean_above(m: u64, count: u64) -> bool {
    forall|i: u64| count <= i < 64 ==> !bit(m, i)
}

pub open spec fn monitor_wf(s: &MonitorState) -> bool {
    &&& 1 <= s.count <= 64
    // The ancestors of a tag form a chain to the root: each tag is its own ancestor, the root
    // is everyone's ancestor, ancestors are created first, and the relation is transitive.
    &&& forall|t: u64| #![trigger s.ancestors[t as int]] t < s.count ==> {
        &&& bit(s.ancestors[t as int], t)
        &&& bit(s.ancestors[t as int], 0)
        &&& forall|u: u64| u < 64 && bit(s.ancestors[t as int], u) ==> u <= t
        &&& forall|u: u64, w: u64| u < 64 && w < 64 && bit(s.ancestors[t as int], u)
            && bit(s.ancestors[u as int], w) ==> bit(s.ancestors[t as int], w)
    }
    // A shared reference to a cell's bytes points, through `alias`, at its nearest ancestor that
    // is a node of the tree; every other tag is its own alias.
    &&& forall|t: u64| #![trigger s.alias[t as int]] t < s.count ==> if bit(s.cell, t) {
        &&& s.alias[t as int] < t
        &&& !bit(s.cell, s.alias[t as int] as u64)
        &&& bit(s.ancestors[t as int], s.alias[t as int] as u64)
    } else {
        s.alias[t as int] == t
    }
    &&& !bit(s.cell, 0)
    // A frozen interior-mutable reference was written before (it was frozen by a foreign read).
    &&& forall|t: u64| t < 64 && bit(s.frozen, t) && bit(s.interior, t) ==> bit(s.active, t)
    // Exposing records the tag accesses act through, which is never a shared reference to a
    // cell's bytes.
    &&& forall|t: u64| t < 64 && bit(s.exposed, t) ==> !bit(s.cell, t)
    // Only a protected, initialized, Reserved tag is conflicted.
    &&& forall|t: u64| t < 64 && bit(s.conflicted, t) ==> !bit(s.active, t) && !bit(s.frozen, t)
        && bit(s.protected, t) && bit(s.initialized, t)
    // Nothing is recorded for tags that do not exist.
    &&& clean_above(s.valid, s.count as u64)
    &&& clean_above(s.active, s.count as u64)
    &&& clean_above(s.frozen, s.count as u64)
    &&& clean_above(s.conflicted, s.count as u64)
    &&& clean_above(s.interior, s.count as u64)
    &&& clean_above(s.protected, s.count as u64)
    &&& clean_above(s.initialized, s.count as u64)
    &&& clean_above(s.cell, s.count as u64)
    &&& clean_above(s.exposed, s.count as u64)
}

// ---------------------------------------------------------------------------------------------
// Stage 0-1: initialization, retags (tags and ancestry)
// ---------------------------------------------------------------------------------------------

/// The tag that accesses through `t` act through.
pub open spec fn eff(a: AbsState, t: nat) -> nat {
    if a.nodes[t].cell { a.nodes[t].alias } else { t }
}

/// The node a retag creates as tag `n` (Tree Borrows: a child of `parent`, Reserved for a
/// mutable reference and Frozen for a shared one; nothing for a shared reference to a cell's
/// bytes, which acts as `eff(parent)`).
pub open spec fn retag_node(
    a: AbsState,
    parent: nat,
    n: nat,
    covers: bool,
    in_cell: bool,
    is_shared: bool,
    is_protected: bool,
) -> Node {
    let is_cell = is_shared && in_cell && covers;
    Node {
        ancestors: a.nodes[parent].ancestors.insert(n),
        perm: if is_shared && !is_cell {
            Perm::Frozen
        } else {
            Perm::Reserved { conflicted: false, interior: !is_shared && in_cell && covers }
        },
        protected: is_protected && !is_cell,
        initialized: covers && !is_cell,
        cell: is_cell,
        alias: if is_cell { eff(a, parent) } else { n },
        exposed: false,
    }
}

pub open spec fn node_eq(x: Node, y: Node) -> bool {
    &&& x.ancestors =~= y.ancestors
    &&& x.perm == y.perm
    &&& x.protected == y.protected
    &&& x.initialized == y.initialized
    &&& x.cell == y.cell
    &&& x.alias == y.alias
    &&& x.exposed == y.exposed
}

/// `b` is `a` with the nodes of the tags in `changed` replaced; the others are unchanged.
pub open spec fn same_nodes_except(a: AbsState, b: AbsState, changed: ISet<nat>) -> bool {
    forall|t: nat| t < a.count && !changed.contains(t) ==> node_eq(#[trigger] b.nodes[t], a.nodes[t])
}

pub open spec fn retag_spec(
    a: AbsState,
    b: AbsState,
    parent: nat,
    covers: bool,
    in_cell: bool,
    is_shared: bool,
    is_protected: bool,
    r: nat,
) -> bool {
    if parent >= a.count {
        r == parent && b.count == a.count && same_nodes_except(a, b, ISet::empty())
    } else if a.count == 64 {
        r == UNKNOWN_TAG && b.count == a.count && same_nodes_except(a, b, ISet::empty())
    } else {
        &&& r == a.count
        &&& b.count == a.count + 1
        &&& same_nodes_except(a, b, ISet::empty())
        &&& node_eq(b.nodes[r], retag_node(a, parent, r, covers, in_cell, is_shared, is_protected))
    }
}

/// Bit `i` of a mask with bit `t` set, cleared or rewritten.
pub proof fn lemma_bit_set(m: u64, t: u64, i: u64)
    requires t < 64, i < 64,
    ensures
        bit(m | (1u64 << t), i) == (i == t || bit(m, i)),
        bit(m & !(1u64 << t), i) == (i != t && bit(m, i)),
{
    lemma_bit_or(m, 1u64 << t, i);
    lemma_bit_and(m, !(1u64 << t), i);
    lemma_bit_not(1u64 << t, i);
    lemma_bit_single(t, i);
}

/// The exec test `m & (1 << t) != 0` is bit `t` of `m`.
pub proof fn lemma_test_bit(m: u64, t: u64)
    requires t < 64,
    ensures (m & (1u64 << t) != 0) == bit(m, t),
{
    assert((m & (1u64 << t) != 0) <==> ((m >> t) & 1u64 == 1u64)) by (bit_vector) requires t < 64;
}

pub proof fn lemma_initialize(s: MonitorState)
    requires
        s.count == 1,
        s.ancestors[0] == 1u64,
        s.valid == 1u64,
        s.active == 1u64,
        s.frozen == 0u64,
        s.conflicted == 0u64,
        s.interior == 0u64,
        s.protected == 0u64,
        s.initialized == 1u64,
        s.cell == 0u64,
        s.alias[0] == 0u8,
        s.exposed == 0u64,
        !s.unknown_exposed,
    ensures monitor_wf(&s), initial_spec(abstraction(&s)),
{
    assert forall|i: u64| i < 64 implies bit(1u64, i) == (i == 0) && !bit(0u64, i) by {
        lemma_bit_one(i);
        lemma_bit_zero(i);
    }
    let a = abstraction(&s);
    assert forall|u: nat| a.nodes[0].ancestors.contains(u) <==> u == 0 by {
        if u < 64 { lemma_bit_one(u as u64); }
    }
}

/// How the bit sets change at bit `i` when `monitor_new_borrow` creates tag `t`.
proof fn lemma_new_borrow_bits(
    s0: MonitorState,
    s: MonitorState,
    t: u64,
    i: u64,
    is_cell: bool,
    is_interior: bool,
    is_initialized: bool,
    is_protected: bool,
    is_frozen: bool,
)
    requires
        t < 64, i < 64,
        s.valid == s0.valid | (1u64 << t),
        s.active == s0.active & !(1u64 << t),
        s.conflicted == s0.conflicted & !(1u64 << t),
        s.exposed == s0.exposed & !(1u64 << t),
        s.cell == if is_cell { s0.cell | (1u64 << t) } else { s0.cell & !(1u64 << t) },
        s.interior == if is_interior { s0.interior | (1u64 << t) } else {
            s0.interior & !(1u64 << t) },
        s.initialized == if is_initialized { s0.initialized | (1u64 << t) } else {
            s0.initialized & !(1u64 << t) },
        s.protected == if is_protected { s0.protected | (1u64 << t) } else {
            s0.protected & !(1u64 << t) },
        s.frozen == if is_frozen { s0.frozen | (1u64 << t) } else { s0.frozen & !(1u64 << t) },
    ensures
        bit(s.valid, i) == (i == t || bit(s0.valid, i)),
        bit(s.active, i) == (i != t && bit(s0.active, i)),
        bit(s.conflicted, i) == (i != t && bit(s0.conflicted, i)),
        bit(s.exposed, i) == (i != t && bit(s0.exposed, i)),
        bit(s.cell, i) == if i == t { is_cell } else { bit(s0.cell, i) },
        bit(s.interior, i) == if i == t { is_interior } else { bit(s0.interior, i) },
        bit(s.initialized, i) == if i == t { is_initialized } else { bit(s0.initialized, i) },
        bit(s.protected, i) == if i == t { is_protected } else { bit(s0.protected, i) },
        bit(s.frozen, i) == if i == t { is_frozen } else { bit(s0.frozen, i) },
{
    lemma_bit_set(s0.valid, t, i);
    lemma_bit_set(s0.active, t, i);
    lemma_bit_set(s0.conflicted, t, i);
    lemma_bit_set(s0.exposed, t, i);
    lemma_bit_set(s0.cell, t, i);
    lemma_bit_set(s0.interior, t, i);
    lemma_bit_set(s0.initialized, t, i);
    lemma_bit_set(s0.protected, t, i);
    lemma_bit_set(s0.frozen, t, i);
}

proof fn lemma_new_borrow(
    s0: MonitorState,
    s: MonitorState,
    parent: u8,
    covers: bool,
    in_cell: bool,
    is_shared: bool,
    is_protected: bool,
)
    requires
        monitor_wf(&s0),
        parent < s0.count,
        s0.count < 64,
        ({
            let t = s0.count as u64;
            let b = 1u64 << t;
            let is_cell = is_shared && in_cell && covers;
            &&& s.count == s0.count + 1
            &&& s.ancestors@ == s0.ancestors@.update(t as int, s0.ancestors[parent as int] | b)
            &&& s.valid == s0.valid | b
            &&& s.active == s0.active & !b
            &&& s.conflicted == s0.conflicted & !b
            &&& s.exposed == s0.exposed & !b
            &&& s.alias@ == s0.alias@.update(t as int, if is_cell {
                    if s0.cell & (1u64 << parent) != 0 { s0.alias[parent as int] } else { parent }
                } else {
                    t as u8
                })
            &&& s.cell == if is_cell { s0.cell | b } else { s0.cell & !b }
            &&& s.interior == if !is_shared && in_cell && covers { s0.interior | b } else {
                    s0.interior & !b }
            &&& s.initialized == if covers && !is_cell { s0.initialized | b } else {
                    s0.initialized & !b }
            &&& s.protected == if is_protected && !is_cell { s0.protected | b } else {
                    s0.protected & !b }
            &&& s.frozen == if is_shared && !is_cell { s0.frozen | b } else { s0.frozen & !b }
        }),
    ensures
        monitor_wf(&s),
        retag_spec(abstraction(&s0), abstraction(&s), parent as nat, covers, in_cell, is_shared,
            is_protected, s0.count as nat),
{
    let t = s0.count as u64;
    let p = parent as u64;
    let is_cell = is_shared && in_cell && covers;
    let is_interior = !is_shared && in_cell && covers;
    let is_initialized = covers && !is_cell;
    let is_prot = is_protected && !is_cell;
    let is_frozen = is_shared && !is_cell;
    assert forall|i: u64| i < 64 implies {
        &&& bit(s.valid, i) == (i == t || bit(s0.valid, i))
        &&& bit(s.active, i) == (i != t && bit(s0.active, i))
        &&& bit(s.conflicted, i) == (i != t && bit(s0.conflicted, i))
        &&& bit(s.exposed, i) == (i != t && bit(s0.exposed, i))
        &&& bit(s.cell, i) == if i == t { is_cell } else { bit(s0.cell, i) }
        &&& bit(s.interior, i) == if i == t { is_interior } else { bit(s0.interior, i) }
        &&& bit(s.initialized, i) == if i == t { is_initialized } else { bit(s0.initialized, i) }
        &&& bit(s.protected, i) == if i == t { is_prot } else { bit(s0.protected, i) }
        &&& bit(s.frozen, i) == if i == t { is_frozen } else { bit(s0.frozen, i) }
    } by {
        lemma_new_borrow_bits(s0, s, t, i, is_cell, is_interior, is_initialized, is_prot,
            is_frozen);
    }
    assert forall|i: u64| i < 64 implies
        bit(s0.ancestors[p as int] | (1u64 << t), i) == (i == t || bit(s0.ancestors[p as int], i))
    by {
        lemma_bit_set(s0.ancestors[p as int], t, i);
    }
    lemma_test_bit(s0.cell, p);
    // Tags other than the new one keep their ancestors and aliases.
    assert forall|u: u64| u < t implies s.ancestors[u as int] == s0.ancestors[u as int]
        && s.alias[u as int] == s0.alias[u as int] by {}
    let ap = s0.ancestors[p as int];
    assert(s.ancestors[t as int] == ap | (1u64 << t));
    // The new tag's ancestors: itself and its parent's.
    assert forall|u: u64| u < 64 implies
        bit(s.ancestors[t as int], u) == (u == t || bit(ap, u)) by {
        lemma_bit_set(ap, t, u);
    }
    assert(bit(ap, p) && bit(ap, 0));
    assert forall|u: u64| u < 64 && bit(ap, u) implies u <= p by {}
    // wf: the tree.
    assert forall|x: u64| #![trigger s.ancestors[x as int]] x < s.count implies {
        &&& bit(s.ancestors[x as int], x)
        &&& bit(s.ancestors[x as int], 0)
        &&& forall|u: u64| u < 64 && bit(s.ancestors[x as int], u) ==> u <= x
        &&& forall|u: u64, w: u64| u < 64 && w < 64 && bit(s.ancestors[x as int], u)
            && bit(s.ancestors[u as int], w) ==> bit(s.ancestors[x as int], w)
    } by {
        if x < t {
            assert(s.ancestors[x as int] == s0.ancestors[x as int]);
            assert(bit(s0.ancestors[x as int], x) && bit(s0.ancestors[x as int], 0));
            assert forall|u: u64| u < 64 && bit(s.ancestors[x as int], u) implies u <= x by {
                assert(bit(s0.ancestors[x as int], u));
            }
            assert forall|u: u64, w: u64| u < 64 && w < 64 && bit(s.ancestors[x as int], u)
                && bit(s.ancestors[u as int], w) implies bit(s.ancestors[x as int], w) by {
                assert(bit(s0.ancestors[x as int], u));
                assert(u <= x);
                assert(s.ancestors[u as int] == s0.ancestors[u as int]);
            }
        } else {
            assert(x == t);
            lemma_bit_set(ap, t, t);
            lemma_bit_set(ap, t, 0);
            assert(bit(s.ancestors[x as int], x));
            assert(bit(s.ancestors[x as int], 0));
            assert forall|u: u64| u < 64 && bit(s.ancestors[x as int], u) implies u <= x by {
                if u != t {
                    assert(bit(ap, u));
                }
            }
            assert forall|u: u64, w: u64| u < 64 && w < 64 && bit(s.ancestors[x as int], u)
                && bit(s.ancestors[u as int], w) implies bit(s.ancestors[x as int], w) by {
                if u != t {
                    assert(bit(ap, u));
                    assert(u <= p);
                    assert(s.ancestors[u as int] == s0.ancestors[u as int]);
                    assert(bit(s0.ancestors[p as int], w));
                }
            }
        }
    }
    // wf: aliases.
    assert forall|x: u64| #![trigger s.alias[x as int]] x < s.count implies if bit(s.cell, x) {
        &&& s.alias[x as int] < x
        &&& !bit(s.cell, s.alias[x as int] as u64)
        &&& bit(s.ancestors[x as int], s.alias[x as int] as u64)
    } else {
        s.alias[x as int] == x
    } by {
        if x < t {
            assert(s.alias[x as int] == s0.alias[x as int]);
            assert(bit(s.cell, x) == bit(s0.cell, x));
            if bit(s0.cell, x) {
                assert(s0.alias[x as int] < x);
                assert(bit(s.cell, s.alias[x as int] as u64) == bit(s0.cell, s0.alias[x as int] as u64));
            }
        } else {
            assert(x == t);
            if is_cell && bit(s0.cell, p) {
                let q = s0.alias[p as int] as u64;
                assert(q < p && !bit(s0.cell, q) && bit(ap, q));
                assert(bit(s.cell, q) == bit(s0.cell, q));
            } else if is_cell {
                assert(bit(s.cell, p) == bit(s0.cell, p));
            }
        }
    }
    assert(!bit(s.cell, 0));
    assert forall|i: u64| t + 1 <= i < 64 implies !bit(s.valid, i) && !bit(s.active, i)
        && !bit(s.frozen, i) && !bit(s.conflicted, i) && !bit(s.interior, i)
        && !bit(s.protected, i) && !bit(s.initialized, i) && !bit(s.cell, i)
        && !bit(s.exposed, i) by {}
    assert forall|i: u64| i < 64 && bit(s.frozen, i) && bit(s.interior, i) implies bit(s.active, i) by {
        if i != t {
            assert(bit(s0.frozen, i) && bit(s0.interior, i));
        }
    }
    // The refinement.
    let a = abstraction(&s0);
    let b = abstraction(&s);
    assert forall|x: nat| x < a.count implies node_eq(#[trigger] b.nodes[x], a.nodes[x]) by {
        assert(s.ancestors[x as int] == s0.ancestors[x as int]);
        assert(mask_set(s.ancestors[x as int]) =~= mask_set(s0.ancestors[x as int]));
    }
    assert(b.nodes[t as nat].ancestors =~= a.nodes[parent as nat].ancestors.insert(t as nat));
}

// ---------------------------------------------------------------------------------------------
// Stages 2-7 and 9: accesses (Tree Borrows' transitions at one location)
// ---------------------------------------------------------------------------------------------

/// Tree Borrows' transition of a node for an access that is local to it (the access goes
/// through the node or one of its descendants). `None`: undefined behavior.
pub open spec fn local_step(n: Node, is_write: bool) -> Option<Node> {
    let prot = n.protected && n.initialized;
    match n.perm {
        Perm::Disabled => None,
        Perm::Frozen => if is_write { None } else { Some(Node { initialized: true, ..n }) },
        Perm::Active => Some(Node { initialized: true, ..n }),
        Perm::Reserved { conflicted, interior } => if !is_write {
            Some(Node { initialized: true, ..n })
        } else if conflicted && prot {
            None
        } else {
            Some(Node { perm: Perm::Active, initialized: true, ..n })
        },
    }
}

/// Tree Borrows' transition of a node for a foreign access. A protected node with an
/// initialized permission must not become Disabled.
pub open spec fn foreign_step(n: Node, is_write: bool) -> Option<Node> {
    let prot = n.protected && n.initialized;
    match n.perm {
        Perm::Disabled => Some(n),
        Perm::Frozen => if !is_write { Some(n) } else if prot { None } else {
            Some(Node { perm: Perm::Disabled, ..n })
        },
        Perm::Active => if !is_write {
            Some(Node { perm: Perm::Frozen, ..n })
        } else if prot {
            None
        } else {
            Some(Node { perm: Perm::Disabled, ..n })
        },
        Perm::Reserved { conflicted, interior } => if !is_write {
            if prot { Some(Node { perm: Perm::Reserved { conflicted: true, interior }, ..n }) }
            else { Some(n) }
        } else if interior {
            Some(n)
        } else if prot {
            None
        } else {
            Some(Node { perm: Perm::Disabled, ..n })
        },
    }
}

/// The transition of node `t` for an access through `e`. A shared reference to a cell's bytes
/// is not a node at this location and never changes.
pub open spec fn node_step(a: AbsState, e: nat, t: nat, is_write: bool) -> Option<Node> {
    if a.nodes[t].cell {
        Some(a.nodes[t])
    } else if a.nodes[e].ancestors.contains(t) {
        local_step(a.nodes[t], is_write)
    } else {
        foreign_step(a.nodes[t], is_write)
    }
}

/// An access through tag `tag` is undefined behavior if any node's transition is.
pub open spec fn access_ub(a: AbsState, tag: nat, is_write: bool) -> bool {
    exists|t: nat| t < a.count && #[trigger] node_step(a, eff(a, tag), t, is_write) is None
}

/// The bits `monitor_access` computes from the tag `e` it acts through.
pub open spec fn access_local(s: &MonitorState, e: u64) -> u64 {
    s.ancestors[e as int] & !s.cell
}

pub open spec fn access_foreign(s: &MonitorState, e: u64) -> u64 {
    s.valid & !s.ancestors[e as int] & !s.cell
}

proof fn lemma_access_masks(s: MonitorState, e: u64, i: u64)
    requires i < 64,
    ensures
        bit(access_local(&s, e), i) == (bit(s.ancestors[e as int], i) && !bit(s.cell, i)),
        bit(access_foreign(&s, e), i)
            == (bit(s.valid, i) && !bit(s.ancestors[e as int], i) && !bit(s.cell, i)),
{
    lemma_bit_and(s.ancestors[e as int], !s.cell, i);
    lemma_bit_not(s.cell, i);
    lemma_bit_and(s.valid, !s.ancestors[e as int], i);
    lemma_bit_and(s.valid & !s.ancestors[e as int], !s.cell, i);
    lemma_bit_not(s.ancestors[e as int], i);
}

/// The tag `monitor_access` acts through is `eff`, and it is a node of the tree.
proof fn lemma_access_eff(s: MonitorState, tag: u8, e: u8)
    requires
        monitor_wf(&s),
        tag < s.count,
        e == if s.cell & (1u64 << tag) != 0 { s.alias[tag as int] } else { tag },
    ensures
        e as nat == eff(abstraction(&s), tag as nat),
        e < s.count,
        !bit(s.cell, e as u64),
{
    lemma_test_bit(s.cell, tag as u64);
    assert(s.alias[tag as int] == s.alias[tag as int]);
}

/// A tag in the path of `e` is a tag.
proof fn lemma_local_is_tag(s: MonitorState, e: u64, i: u64)
    requires monitor_wf(&s), e < s.count, i < 64, bit(s.ancestors[e as int], i),
    ensures i <= e, i < s.count,
{
    assert(s.ancestors[e as int] == s.ancestors[e as int]);
}

/// UB witness: a disabled tag on the path.
proof fn lemma_access_ub_invalid(s: MonitorState, tag: u8, e: u8, is_write: bool)
    requires
        monitor_wf(&s), tag < s.count, e as nat == eff(abstraction(&s), tag as nat), e < s.count,
        s.valid & access_local(&s, e as u64) != access_local(&s, e as u64),
    ensures access_ub(abstraction(&s), tag as nat, is_write),
{
    let l = access_local(&s, e as u64);
    lemma_subset(s.valid, l);
    let i = choose|i: u64| i < 64 && bit(l, i) && !bit(s.valid, i);
    lemma_access_masks(s, e as u64, i);
    lemma_local_is_tag(s, e as u64, i);
    let a = abstraction(&s);
    assert(a.nodes[e as nat].ancestors.contains(i as nat));
    assert(node_step(a, eff(a, tag as nat), i as nat, is_write) is None);
}

/// UB witness: a write through a path with a frozen tag.
proof fn lemma_access_ub_frozen(s: MonitorState, tag: u8, e: u8)
    requires
        monitor_wf(&s), tag < s.count, e as nat == eff(abstraction(&s), tag as nat), e < s.count,
        s.valid & access_local(&s, e as u64) == access_local(&s, e as u64),
        s.frozen & access_local(&s, e as u64) != 0,
    ensures access_ub(abstraction(&s), tag as nat, true),
{
    let l = access_local(&s, e as u64);
    lemma_subset(s.valid, l);
    lemma_and_nonzero(s.frozen, l);
    let i = choose|i: u64| i < 64 && bit(s.frozen, i) && bit(l, i);
    lemma_access_masks(s, e as u64, i);
    lemma_local_is_tag(s, e as u64, i);
    let a = abstraction(&s);
    assert(a.nodes[e as nat].ancestors.contains(i as nat));
    assert(node_step(a, eff(a, tag as nat), i as nat, true) is None);
}

/// UB witness: a write that disables, or activates a conflicted, protected tag.
proof fn lemma_access_ub_protector(s: MonitorState, tag: u8, e: u8)
    requires
        monitor_wf(&s), tag < s.count, e as nat == eff(abstraction(&s), tag as nat), e < s.count,
        s.valid & access_local(&s, e as u64) == access_local(&s, e as u64),
        s.frozen & access_local(&s, e as u64) == 0,
        (s.protected & s.initialized) & ((access_foreign(&s, e as u64) & !(s.interior & !s.active))
            | (s.conflicted & access_local(&s, e as u64))) != 0,
    ensures access_ub(abstraction(&s), tag as nat, true),
{
    let l = access_local(&s, e as u64);
    let f = access_foreign(&s, e as u64);
    let d = f & !(s.interior & !s.active);
    let pi = s.protected & s.initialized;
    lemma_and_nonzero(pi, d | (s.conflicted & l));
    let i = choose|i: u64| i < 64 && bit(pi, i) && bit(d | (s.conflicted & l), i);
    lemma_access_masks(s, e as u64, i);
    lemma_bit_and(s.protected, s.initialized, i);
    lemma_bit_or(d, s.conflicted & l, i);
    lemma_bit_and(s.conflicted, l, i);
    lemma_bit_and(f, !(s.interior & !s.active), i);
    lemma_bit_not(s.interior & !s.active, i);
    lemma_bit_and(s.interior, !s.active, i);
    lemma_bit_not(s.active, i);
    lemma_subset(s.valid, l);
    let a = abstraction(&s);
    if bit(d, i) {
        assert(i < s.count) by {
            if i >= s.count { assert(!bit(s.valid, i)); }
        }
        assert(!a.nodes[e as nat].ancestors.contains(i as nat));
        assert(node_step(a, eff(a, tag as nat), i as nat, true) is None);
    } else {
        lemma_local_is_tag(s, e as u64, i);
        assert(a.nodes[e as nat].ancestors.contains(i as nat));
        assert(node_step(a, eff(a, tag as nat), i as nat, true) is None);
    }
}

/// The state after a successful access through `e`.
pub open spec fn access_post_state(s0: &MonitorState, s: &MonitorState, e: u64, is_write: bool) -> bool {
    let l = access_local(s0, e);
    let f = access_foreign(s0, e);
    let pi = s0.protected & s0.initialized;
    &&& s.count == s0.count
    &&& s.ancestors == s0.ancestors
    &&& s.alias == s0.alias
    &&& s.cell == s0.cell
    &&& s.interior == s0.interior
    &&& s.protected == s0.protected
    &&& s.exposed == s0.exposed
    &&& s.unknown_exposed == s0.unknown_exposed
    &&& s.initialized == s0.initialized | l
    &&& if is_write {
        &&& s.valid == s0.valid & !(f & !(s0.interior & !s0.active))
        &&& s.active == s0.active | l
        &&& s.frozen == s0.frozen
        &&& s.conflicted == s0.conflicted
    } else {
        &&& s.valid == s0.valid
        &&& s.active == s0.active
        &&& s.conflicted == s0.conflicted | (pi & f & !s0.active & !s0.frozen)
        &&& s.frozen == s0.frozen | (s0.active & f)
    }
}

/// The absence of the conditions `monitor_access` rejects.
pub open spec fn access_allowed(s0: &MonitorState, e: u64, is_write: bool) -> bool {
    let l = access_local(s0, e);
    let f = access_foreign(s0, e);
    let pi = s0.protected & s0.initialized;
    &&& s0.valid & l == l
    &&& is_write ==> s0.frozen & l == 0
    &&& is_write ==> pi & ((f & !(s0.interior & !s0.active)) | (s0.conflicted & l)) == 0
}

/// One node after a successful access is Tree Borrows' transition of it.
proof fn lemma_access_node(s0: MonitorState, s: MonitorState, e: u64, is_write: bool, t: u64)
    requires
        monitor_wf(&s0), e < s0.count, !bit(s0.cell, e), t < s0.count,
        access_allowed(&s0, e, is_write),
        access_post_state(&s0, &s, e, is_write),
    ensures ({
        let a = abstraction(&s0);
        &&& node_step(a, e as nat, t as nat, is_write) is Some
        &&& node_eq(node_of(&s, t), node_step(a, e as nat, t as nat, is_write)->Some_0)
    }),
{
    let l = access_local(&s0, e);
    let f = access_foreign(&s0, e);
    let pi = s0.protected & s0.initialized;
    let d = f & !(s0.interior & !s0.active);
    lemma_access_masks(s0, e, t);
    lemma_bit_and(s0.protected, s0.initialized, t);
    lemma_bit_or(s0.initialized, l, t);
    lemma_bit_and(f, !(s0.interior & !s0.active), t);
    lemma_bit_not(s0.interior & !s0.active, t);
    lemma_bit_and(s0.interior, !s0.active, t);
    lemma_bit_not(s0.active, t);
    lemma_bit_and(s0.valid, !d, t);
    lemma_bit_not(d, t);
    lemma_bit_or(s0.active, l, t);
    lemma_bit_and(pi, f, t);
    lemma_bit_and(pi & f, !s0.active, t);
    lemma_bit_and(pi & f & !s0.active, !s0.frozen, t);
    lemma_bit_not(s0.frozen, t);
    lemma_bit_or(s0.conflicted, pi & f & !s0.active & !s0.frozen, t);
    lemma_bit_and(s0.active, f, t);
    lemma_bit_or(s0.frozen, s0.active & f, t);
    lemma_subset(s0.valid, l);
    if is_write {
        lemma_and_nonzero(s0.frozen, l);
        lemma_and_nonzero(pi, d | (s0.conflicted & l));
        lemma_bit_or(d, s0.conflicted & l, t);
        lemma_bit_and(s0.conflicted, l, t);
    }
    let a = abstraction(&s0);
    assert(a.nodes[e as nat].ancestors.contains(t as nat) == bit(s0.ancestors[e as int], t));
    assert(mask_set(s.ancestors[t as int]) =~= mask_set(s0.ancestors[t as int]));
}

/// A successful access refines Tree Borrows and keeps the state well-formed.
proof fn lemma_access_ok(s0: MonitorState, s: MonitorState, tag: u8, e: u8, is_write: bool)
    requires
        monitor_wf(&s0), tag < s0.count, e as nat == eff(abstraction(&s0), tag as nat),
        e < s0.count, !bit(s0.cell, e as u64),
        access_allowed(&s0, e as u64, is_write),
        access_post_state(&s0, &s, e as u64, is_write),
    ensures
        monitor_wf(&s),
        access_refines(abstraction(&s0), abstraction(&s), tag as nat, is_write, ACCESS_OK),
{
    let a = abstraction(&s0);
    let b = abstraction(&s);
    assert forall|t: nat| t < a.count implies {
        &&& node_step(a, eff(a, tag as nat), t, is_write) is Some
        &&& node_eq(#[trigger] b.nodes[t], node_step(a, eff(a, tag as nat), t, is_write)->Some_0)
    } by {
        lemma_access_node(s0, s, e as u64, is_write, t as u64);
    }
    assert forall|t: nat| t < a.count implies
        (#[trigger] node_step(a, eff(a, tag as nat), t, is_write)) is Some by {
        lemma_access_node(s0, s, e as u64, is_write, t as u64);
    }
    assert(!access_ub(a, tag as nat, is_write));
    // Well-formedness: the tree and aliases are unchanged; the permission invariants hold.
    let l = access_local(&s0, e as u64);
    let f = access_foreign(&s0, e as u64);
    assert forall|i: u64| i < 64 implies {
        &&& (bit(s.frozen, i) && bit(s.interior, i) ==> bit(s.active, i))
        &&& (bit(s.conflicted, i) ==> !bit(s.active, i) && !bit(s.frozen, i)
            && bit(s.protected, i) && bit(s.initialized, i))
        &&& (s0.count <= i ==> !bit(s.valid, i) && !bit(s.active, i) && !bit(s.frozen, i)
            && !bit(s.conflicted, i) && !bit(s.initialized, i))
    } by {
        if i < s0.count {
            lemma_access_node(s0, s, e as u64, is_write, i);
        }
        lemma_access_masks(s0, e as u64, i);
        let pi = s0.protected & s0.initialized;
        let d = f & !(s0.interior & !s0.active);
        lemma_bit_and(s0.protected, s0.initialized, i);
        lemma_bit_or(s0.initialized, l, i);
        lemma_bit_and(f, !(s0.interior & !s0.active), i);
        lemma_bit_not(s0.interior & !s0.active, i);
        lemma_bit_and(s0.interior, !s0.active, i);
        lemma_bit_not(s0.active, i);
        lemma_bit_and(s0.valid, !d, i);
        lemma_bit_not(d, i);
        lemma_bit_or(s0.active, l, i);
        lemma_bit_and(pi, f, i);
        lemma_bit_and(pi & f, !s0.active, i);
        lemma_bit_and(pi & f & !s0.active, !s0.frozen, i);
        lemma_bit_not(s0.frozen, i);
        lemma_bit_or(s0.conflicted, pi & f & !s0.active & !s0.frozen, i);
        lemma_bit_and(s0.active, f, i);
        lemma_bit_or(s0.frozen, s0.active & f, i);
        if s0.count <= i {
            if bit(s0.ancestors[e as int], i) { lemma_local_is_tag(s0, e as u64, i); }
        }
        if is_write {
            lemma_and_nonzero(pi, d | (s0.conflicted & l));
            lemma_bit_or(d, s0.conflicted & l, i);
            lemma_bit_and(s0.conflicted, l, i);
        }
    }
}

pub open spec fn access_refines(
    before: AbsState,
    after: AbsState,
    tag: nat,
    is_write: bool,
    code: u8,
) -> bool {
    &&& (code == ACCESS_OK) == !access_ub(before, tag, is_write)
    &&& code != ACCESS_OK ==> code == ACCESS_INVALIDATED || code == ACCESS_WRITE_FROZEN
        || code == ACCESS_PROTECTOR
    &&& code == ACCESS_OK ==> {
        &&& after.count == before.count
        &&& forall|t: nat| t < before.count ==> node_eq(#[trigger] after.nodes[t],
                node_step(before, eff(before, tag), t, is_write)->Some_0)
    }
}

// ---------------------------------------------------------------------------------------------
// Stages 10-11: deallocation under a protector, exposed provenance
// ---------------------------------------------------------------------------------------------

/// Deallocating the tracked location is undefined behavior if a protected tag has an
/// initialized permission there that is not Disabled.
pub open spec fn dealloc_ub(a: AbsState) -> bool {
    exists|t: nat| t < a.count && {
        let n = #[trigger] a.nodes[t];
        !n.cell && n.perm != Perm::Disabled && n.protected && n.initialized
    }
}

proof fn lemma_dealloc(s: MonitorState)
    requires monitor_wf(&s),
    ensures (s.protected & s.initialized & s.valid & !s.cell != 0) == dealloc_ub(abstraction(&s)),
{
    let m = s.protected & s.initialized & s.valid & !s.cell;
    let a = abstraction(&s);
    assert forall|i: u64| i < 64 implies bit(m, i) == (bit(s.protected, i) && bit(s.initialized, i)
        && bit(s.valid, i) && !bit(s.cell, i)) by {
        lemma_bit_and(s.protected, s.initialized, i);
        lemma_bit_and(s.protected & s.initialized, s.valid, i);
        lemma_bit_and(s.protected & s.initialized & s.valid, !s.cell, i);
        lemma_bit_not(s.cell, i);
    }
    if m != 0 {
        lemma_nonzero_witness(m);
        let i = choose|i: u64| i < 64 && bit(m, i);
        assert(i < s.count) by { if i >= s.count { assert(!bit(s.valid, i)); } }
        assert(a.nodes[i as nat].perm != Perm::Disabled);
    } else {
        assert forall|t: nat| t < a.count implies !({
            let n = #[trigger] a.nodes[t];
            !n.cell && n.perm != Perm::Disabled && n.protected && n.initialized
        }) by {
            lemma_bit_zero(t as u64);
        }
    }
}

/// Exposing the pointer tagged `tag` exposes the tag accesses through it act through; exposing a
/// pointer with an unknown tag is recorded as such.
pub open spec fn expose_spec(a: AbsState, b: AbsState, tag: nat) -> bool {
    &&& b.count == a.count
    &&& if tag < a.count {
        &&& b.unknown_exposed == a.unknown_exposed
        &&& same_nodes_except(a, b, iset![eff(a, tag)])
        &&& node_eq(b.nodes[eff(a, tag)], Node { exposed: true, ..a.nodes[eff(a, tag)] })
    } else {
        &&& b.unknown_exposed == (a.unknown_exposed || tag != EXPOSED_TAG)
        &&& same_nodes_except(a, b, ISet::empty())
    }
}

proof fn lemma_expose(s0: MonitorState, s: MonitorState, tag: u8, e: u8)
    requires
        monitor_wf(&s0), tag < s0.count,
        e == if s0.cell & (1u64 << tag) != 0 { s0.alias[tag as int] } else { tag },
        s == (MonitorState { exposed: s0.exposed | (1u64 << e), ..s0 }),
    ensures monitor_wf(&s), expose_spec(abstraction(&s0), abstraction(&s), tag as nat),
{
    lemma_access_eff(s0, tag, e);
    assert forall|i: u64| i < 64 implies bit(s.exposed, i) == (i == e || bit(s0.exposed, i)) by {
        lemma_bit_set(s0.exposed, e as u64, i);
    }
    let a = abstraction(&s0);
    let b = abstraction(&s);
    assert forall|t: nat| t < a.count && !iset![eff(a, tag as nat)].contains(t) implies
        node_eq(#[trigger] b.nodes[t], a.nodes[t]) by {}
}

// ---------------------------------------------------------------------------------------------
// Returns: protectors end, unreachable tags are dropped
// ---------------------------------------------------------------------------------------------

/// The number of tags kept when a function that started with `frame` tags returns `kept`:
/// the tags created before it, and the ones up to the last returned tag it created.
pub open spec fn kept_count(count: nat, frame: nat, kept: Seq<u8>) -> nat {
    let step = |c: nat, k: u8| if frame <= k && (k as nat) < count && c <= k { k as nat + 1 } else { c };
    let c = step(step(step(step(frame, kept[0]), kept[1]), kept[2]), kept[3]);
    if c < count { c } else { count }
}

/// A tag created by the returning function stops being protected (and so conflicted).
pub open spec fn unprotect(n: Node) -> Node {
    Node {
        protected: false,
        perm: match n.perm {
            Perm::Reserved { conflicted, interior } => Perm::Reserved { conflicted: false, interior },
            p => p,
        },
        ..n
    }
}

pub open spec fn return_spec(a: AbsState, b: AbsState, frame: nat, kept: Seq<u8>) -> bool {
    &&& b.count == kept_count(a.count, frame, kept)
    &&& b.unknown_exposed == a.unknown_exposed
    &&& forall|t: nat| t < b.count ==> node_eq(#[trigger] b.nodes[t],
            if frame < 64 && t >= frame { unprotect(a.nodes[t]) } else { a.nodes[t] })
}

pub proof fn lemma_shift_pos(f: u64)
    requires f < 64,
    ensures (1u64 << f) >= 1,
{
    assert((1u64 << f) >= 1u64) by (bit_vector) requires f < 64;
}

proof fn lemma_return(s0: MonitorState, s1: MonitorState, s: MonitorState, frame: u8, kept: [u8; 4],
    count: u8)
    requires
        monitor_wf(&s0),
        frame >= 1,
        // Protection ends.
        s1 == if frame < 64 {
            MonitorState {
                protected: s0.protected & (((1u64 << frame) - 1u64) as u64),
                conflicted: s0.conflicted & (((1u64 << frame) - 1u64) as u64),
                ..s0
            }
        } else {
            s0
        },
        count as nat == {
            let step = |c: nat, k: u8| if frame <= k && k < s0.count && c <= k { k as nat + 1 } else { c };
            step(step(step(step(frame as nat, kept[0]), kept[1]), kept[2]), kept[3])
        },
        // Unreachable tags are dropped.
        s == if count < s1.count {
            let below = ((1u64 << count) - 1u64) as u64;
            MonitorState {
                count: count,
                valid: s1.valid & below,
                active: s1.active & below,
                frozen: s1.frozen & below,
                conflicted: s1.conflicted & below,
                interior: s1.interior & below,
                protected: s1.protected & below,
                initialized: s1.initialized & below,
                cell: s1.cell & below,
                exposed: s1.exposed & below,
                ..s1
            }
        } else {
            s1
        },
    ensures
        monitor_wf(&s),
        return_spec(abstraction(&s0), abstraction(&s), frame as nat, kept@),
{
    // Bits below the frame and below the new count.
    assert forall|i: u64| i < 64 implies {
        &&& bit(s1.protected, i) == (bit(s0.protected, i) && (frame >= 64 || i < frame))
        &&& bit(s1.conflicted, i) == (bit(s0.conflicted, i) && (frame >= 64 || i < frame))
    } by {
        if frame < 64 {
            lemma_bit_below(frame as u64, i);
            lemma_bit_and(s0.protected, ((1u64 << frame) - 1u64) as u64, i);
            lemma_bit_and(s0.conflicted, ((1u64 << frame) - 1u64) as u64, i);
        }
    }
    let n = s.count;
    assert(n >= 1);
    assert(n <= s0.count);
    assert forall|i: u64| i < 64 implies {
        &&& bit(s.valid, i) == (bit(s1.valid, i) && i < n)
        &&& bit(s.active, i) == (bit(s1.active, i) && i < n)
        &&& bit(s.frozen, i) == (bit(s1.frozen, i) && i < n)
        &&& bit(s.conflicted, i) == (bit(s1.conflicted, i) && i < n)
        &&& bit(s.interior, i) == (bit(s1.interior, i) && i < n)
        &&& bit(s.protected, i) == (bit(s1.protected, i) && i < n)
        &&& bit(s.initialized, i) == (bit(s1.initialized, i) && i < n)
        &&& bit(s.cell, i) == (bit(s1.cell, i) && i < n)
        &&& bit(s.exposed, i) == (bit(s1.exposed, i) && i < n)
    } by {
        if count < s1.count {
            let below = ((1u64 << count) - 1u64) as u64;
            lemma_bit_below(count as u64, i);
            lemma_bit_and(s1.valid, below, i);
            lemma_bit_and(s1.active, below, i);
            lemma_bit_and(s1.frozen, below, i);
            lemma_bit_and(s1.conflicted, below, i);
            lemma_bit_and(s1.interior, below, i);
            lemma_bit_and(s1.protected, below, i);
            lemma_bit_and(s1.initialized, below, i);
            lemma_bit_and(s1.cell, below, i);
            lemma_bit_and(s1.exposed, below, i);
        } else {
            if i >= n {
                assert(!bit(s0.valid, i) && !bit(s0.active, i) && !bit(s0.frozen, i)
                    && !bit(s0.conflicted, i) && !bit(s0.interior, i) && !bit(s0.protected, i)
                    && !bit(s0.initialized, i) && !bit(s0.cell, i) && !bit(s0.exposed, i));
            }
        }
    }
    // Well-formedness: the remaining tags keep their ancestors and aliases.
    assert forall|t: u64| #![trigger s.ancestors[t as int]] t < s.count implies {
        &&& bit(s.ancestors[t as int], t)
        &&& bit(s.ancestors[t as int], 0)
        &&& forall|u: u64| u < 64 && bit(s.ancestors[t as int], u) ==> u <= t
        &&& forall|u: u64, w: u64| u < 64 && w < 64 && bit(s.ancestors[t as int], u)
            && bit(s.ancestors[u as int], w) ==> bit(s.ancestors[t as int], w)
    } by {
        assert(s0.ancestors[t as int] == s0.ancestors[t as int]);
    }
    assert forall|t: u64| #![trigger s.alias[t as int]] t < s.count implies if bit(s.cell, t) {
        &&& s.alias[t as int] < t
        &&& !bit(s.cell, s.alias[t as int] as u64)
        &&& bit(s.ancestors[t as int], s.alias[t as int] as u64)
    } else {
        s.alias[t as int] == t
    } by {
        assert(s0.alias[t as int] == s0.alias[t as int]);
    }
    let a = abstraction(&s0);
    let b = abstraction(&s);
    assert forall|t: nat| t < b.count implies node_eq(#[trigger] b.nodes[t],
        if frame < 64 && t >= frame { unprotect(a.nodes[t]) } else { a.nodes[t] }) by {
        assert(mask_set(s.ancestors[t as int]) =~= mask_set(s0.ancestors[t as int]));
    }
}

// ---------------------------------------------------------------------------------------------
// Stage 11: accesses through pointers created from integers (Tree Borrows' wildcard accesses)
// ---------------------------------------------------------------------------------------------

/// Exposed tag `e` allows an access: it and every tag on its path are not Disabled, and for a
/// write, none of them is Frozen.
pub open spec fn wild_cand(a: AbsState, e: nat, is_write: bool) -> bool {
    &&& e < a.count
    &&& !a.nodes[e].cell
    &&& a.nodes[e].exposed
    &&& forall|u: nat| #![trigger a.nodes[u]] u < a.count && a.nodes[e].ancestors.contains(u)
        && !a.nodes[u].cell ==> a.nodes[u].perm != Perm::Disabled
            && (is_write ==> a.nodes[u].perm != Perm::Frozen)
}

/// Node `t` is on the path of some exposed tag that allows the access.
pub open spec fn wild_local(a: AbsState, t: nat, is_write: bool) -> bool {
    exists|e: nat| wild_cand(a, e, is_write) && #[trigger] a.nodes[e].ancestors.contains(t)
}

/// A wildcard access only changes the nodes that are foreign to every allowing exposed tag.
pub open spec fn wild_step(a: AbsState, t: nat, is_write: bool) -> Option<Node> {
    if a.nodes[t].cell || wild_local(a, t, is_write) {
        Some(a.nodes[t])
    } else {
        foreign_step(a.nodes[t], is_write)
    }
}

pub open spec fn wildcard_refines(a: AbsState, b: AbsState, is_write: bool, code: u8) -> bool {
    if a.unknown_exposed {
        code == ACCESS_UNKNOWN_EXPOSED
    } else {
        &&& (code == ACCESS_NOT_EXPOSED) == !(exists|e: nat| wild_cand(a, e, is_write))
        &&& code == ACCESS_OK || code == ACCESS_NOT_EXPOSED || code == ACCESS_PROTECTOR
        &&& (exists|e: nat| wild_cand(a, e, is_write)) ==> ((code == ACCESS_OK) == forall|t: nat|
                t < a.count ==> (#[trigger] wild_step(a, t, is_write)) is Some)
        &&& code == ACCESS_OK ==> {
            &&& b.count == a.count
            &&& b.unknown_exposed == a.unknown_exposed
            &&& forall|t: nat| t < a.count ==> node_eq(#[trigger] b.nodes[t],
                    wild_step(a, t, is_write)->Some_0)
        }
    }
}

/// The exec test for candidate `e`.
pub open spec fn cand_bits(s: &MonitorState, e: u64, is_write: bool) -> bool {
    let path = s.ancestors[e as int] & !s.cell;
    &&& s.exposed & s.valid & (1u64 << e) != 0
    &&& s.valid & path == path
    &&& (!is_write || s.frozen & path == 0)
}

/// `allowed` and `possibly_local` after considering the candidates `0..k`.
pub open spec fn allowed_upto(s: &MonitorState, is_write: bool, k: nat) -> bool
    decreases k,
{
    if k == 0 { false } else {
        allowed_upto(s, is_write, (k - 1) as nat) || cand_bits(s, (k - 1) as u64, is_write)
    }
}

pub open spec fn local_upto(s: &MonitorState, is_write: bool, k: nat) -> u64
    decreases k,
{
    if k == 0 { 0u64 } else {
        local_upto(s, is_write, (k - 1) as nat)
            | if cand_bits(s, (k - 1) as u64, is_write) { s.ancestors[(k - 1) as int] } else { 0u64 }
    }
}

pub proof fn lemma_or_zero(x: u64)
    ensures x | 0u64 == x,
{
    assert(x | 0u64 == x) by (bit_vector);
}

/// The exec candidate test is `wild_cand`.
proof fn lemma_cand_bits(s: MonitorState, e: u64, is_write: bool)
    requires monitor_wf(&s), e < 64,
    ensures cand_bits(&s, e, is_write) == wild_cand(abstraction(&s), e as nat, is_write),
{
    let path = s.ancestors[e as int] & !s.cell;
    let a = abstraction(&s);
    lemma_test_bit(s.exposed & s.valid, e);
    lemma_bit_and(s.exposed, s.valid, e);
    lemma_subset(s.valid, path);
    lemma_and_nonzero(s.frozen, path);
    assert forall|i: u64| i < 64 implies bit(path, i) == (bit(s.ancestors[e as int], i)
        && !bit(s.cell, i)) by {
        lemma_bit_and(s.ancestors[e as int], !s.cell, i);
        lemma_bit_not(s.cell, i);
    }
    if e < s.count {
        assert forall|u: u64| u < 64 && bit(s.ancestors[e as int], u) implies u < s.count by {
            lemma_local_is_tag(s, e, u);
        }
        if cand_bits(&s, e, is_write) {
            assert(bit(s.ancestors[e as int], e));
            assert forall|u: nat| #![trigger a.nodes[u]] u < a.count
                && a.nodes[e as nat].ancestors.contains(u) && !a.nodes[u].cell implies
                a.nodes[u].perm != Perm::Disabled && (is_write ==> a.nodes[u].perm != Perm::Frozen)
            by {
                assert(bit(path, u as u64));
            }
        }
        if wild_cand(a, e as nat, is_write) {
            assert(bit(s.ancestors[e as int], e));
            assert forall|i: u64| i < 64 && bit(path, i) implies bit(s.valid, i) by {
                assert(a.nodes[i as nat].perm != Perm::Disabled);
            }
            if is_write {
                assert forall|i: u64| !(i < 64 && bit(s.frozen, i) && bit(path, i)) by {
                    if i < 64 && bit(path, i) {
                        assert(a.nodes[i as nat].perm != Perm::Frozen);
                    }
                }
            }
        }
    } else {
        assert(!bit(s.exposed, e));
    }
}

/// The exec candidate loop computes, after all 64 candidates, whether some candidate allows the
/// access and the union of their paths.
proof fn lemma_upto(s: MonitorState, is_write: bool, k: nat)
    requires monitor_wf(&s), k <= 64,
    ensures
        allowed_upto(&s, is_write, k)
            == exists|e: nat| e < k && wild_cand(abstraction(&s), e, is_write),
        forall|t: u64| t < 64 ==> (bit(local_upto(&s, is_write, k), t) == exists|e: nat| e < k
            && wild_cand(abstraction(&s), e, is_write)
            && #[trigger] abstraction(&s).nodes[e].ancestors.contains(t as nat)),
    decreases k,
{
    let a = abstraction(&s);
    if k == 0 {
        assert forall|t: u64| t < 64 implies !bit(local_upto(&s, is_write, 0), t) by {
            lemma_bit_zero(t);
        }
    } else {
        let j = (k - 1) as nat;
        lemma_upto(s, is_write, j);
        lemma_cand_bits(s, j as u64, is_write);
        let prev = local_upto(&s, is_write, j);
        let add = if cand_bits(&s, j as u64, is_write) { s.ancestors[j as int] } else { 0u64 };
        assert forall|t: u64| t < 64 implies (bit(local_upto(&s, is_write, k), t) == exists|e: nat|
            e < k && wild_cand(a, e, is_write) && #[trigger] a.nodes[e].ancestors.contains(t as nat))
        by {
            lemma_bit_or(prev, add, t);
            lemma_bit_zero(t);
            if bit(local_upto(&s, is_write, k), t) {
                if !bit(prev, t) {
                    assert(a.nodes[j].ancestors.contains(t as nat));
                }
            } else {
                assert forall|e: nat| e < k && wild_cand(a, e, is_write) implies
                    !a.nodes[e].ancestors.contains(t as nat) by {
                    if e == j {
                        assert(bit(add, t) == bit(s.ancestors[j as int], t));
                    }
                }
            }
        }
        if allowed_upto(&s, is_write, k) && !allowed_upto(&s, is_write, j) {
            assert(wild_cand(a, j, is_write));
        }
    }
}

/// The bits a wildcard access computes, at bit `i`.
proof fn lemma_wild_bits(s0: MonitorState, pl: u64, i: u64)
    requires i < 64,
    ensures ({
        let f = s0.valid & !pl & !s0.cell;
        let pi = s0.protected & s0.initialized;
        let d = f & !(s0.interior & !s0.active);
        &&& bit(f, i) == (bit(s0.valid, i) && !bit(pl, i) && !bit(s0.cell, i))
        &&& bit(pi, i) == (bit(s0.protected, i) && bit(s0.initialized, i))
        &&& bit(d, i) == (bit(f, i) && !(bit(s0.interior, i) && !bit(s0.active, i)))
        &&& bit(s0.valid & !d, i) == (bit(s0.valid, i) && !bit(d, i))
        &&& bit(pi & d, i) == (bit(pi, i) && bit(d, i))
        &&& bit(s0.conflicted | (pi & f & !s0.active & !s0.frozen), i) == (bit(s0.conflicted, i)
            || (bit(pi, i) && bit(f, i) && !bit(s0.active, i) && !bit(s0.frozen, i)))
        &&& bit(s0.frozen | (s0.active & f), i) == (bit(s0.frozen, i) || (bit(s0.active, i)
            && bit(f, i)))
    }),
{
    let f = s0.valid & !pl & !s0.cell;
    let pi = s0.protected & s0.initialized;
    let d = f & !(s0.interior & !s0.active);
    lemma_bit_and(s0.valid, !pl, i);
    lemma_bit_not(pl, i);
    lemma_bit_and(s0.valid & !pl, !s0.cell, i);
    lemma_bit_not(s0.cell, i);
    lemma_bit_and(s0.protected, s0.initialized, i);
    lemma_bit_and(f, !(s0.interior & !s0.active), i);
    lemma_bit_not(s0.interior & !s0.active, i);
    lemma_bit_and(s0.interior, !s0.active, i);
    lemma_bit_not(s0.active, i);
    lemma_bit_and(s0.valid, !d, i);
    lemma_bit_not(d, i);
    lemma_bit_and(pi, d, i);
    lemma_bit_and(pi, f, i);
    lemma_bit_and(pi & f, !s0.active, i);
    lemma_bit_and(pi & f & !s0.active, !s0.frozen, i);
    lemma_bit_not(s0.frozen, i);
    lemma_bit_or(s0.conflicted, pi & f & !s0.active & !s0.frozen, i);
    lemma_bit_and(s0.active, f, i);
    lemma_bit_or(s0.frozen, s0.active & f, i);
}

/// One node after a successful wildcard access is `wild_step` of it.
proof fn lemma_wild_node(s0: MonitorState, s: MonitorState, is_write: bool, pl: u64, t: u64)
    requires
        monitor_wf(&s0), t < s0.count,
        forall|i: u64| i < 64 ==> bit(pl, i) == wild_local(abstraction(&s0), i as nat, is_write),
        ({
            let f = s0.valid & !pl & !s0.cell;
            let pi = s0.protected & s0.initialized;
            let d = f & !(s0.interior & !s0.active);
            &&& is_write ==> pi & d == 0
            &&& s == if is_write {
                    MonitorState { valid: s0.valid & !d, ..s0 }
                } else {
                    MonitorState {
                        conflicted: s0.conflicted | (pi & f & !s0.active & !s0.frozen),
                        frozen: s0.frozen | (s0.active & f),
                        ..s0
                    }
                }
        }),
    ensures ({
        let a = abstraction(&s0);
        &&& wild_step(a, t as nat, is_write) is Some
        &&& node_eq(node_of(&s, t), wild_step(a, t as nat, is_write)->Some_0)
    }),
{
    let f = s0.valid & !pl & !s0.cell;
    let pi = s0.protected & s0.initialized;
    let d = f & !(s0.interior & !s0.active);
    lemma_bit_and(s0.valid, !pl, t);
    lemma_bit_not(pl, t);
    lemma_bit_and(s0.valid & !pl, !s0.cell, t);
    lemma_bit_not(s0.cell, t);
    lemma_bit_and(s0.protected, s0.initialized, t);
    lemma_bit_and(f, !(s0.interior & !s0.active), t);
    lemma_bit_not(s0.interior & !s0.active, t);
    lemma_bit_and(s0.interior, !s0.active, t);
    lemma_bit_not(s0.active, t);
    lemma_bit_and(s0.valid, !d, t);
    lemma_bit_not(d, t);
    lemma_bit_and(pi, f, t);
    lemma_bit_and(pi & f, !s0.active, t);
    lemma_bit_and(pi & f & !s0.active, !s0.frozen, t);
    lemma_bit_not(s0.frozen, t);
    lemma_bit_or(s0.conflicted, pi & f & !s0.active & !s0.frozen, t);
    lemma_bit_and(s0.active, f, t);
    lemma_bit_or(s0.frozen, s0.active & f, t);
    if is_write {
        lemma_and_nonzero(pi, d);
    }
    assert(mask_set(s.ancestors[t as int]) =~= mask_set(s0.ancestors[t as int]));
}

/// The result of a wildcard access, from `allowed` and `possibly_local` as the exec code computed
/// them.
proof fn lemma_wildcard(s0: MonitorState, s: MonitorState, is_write: bool, pl: u64, code: u8)
    requires
        monitor_wf(&s0),
        !s0.unknown_exposed,
        pl == local_upto(&s0, is_write, 64),
        ({
            let f = s0.valid & !pl & !s0.cell;
            let pi = s0.protected & s0.initialized;
            let d = f & !(s0.interior & !s0.active);
            if !allowed_upto(&s0, is_write, 64) {
                code == ACCESS_NOT_EXPOSED && s == s0
            } else if is_write && pi & d != 0 {
                code == ACCESS_PROTECTOR && s == s0
            } else {
                &&& code == ACCESS_OK
                &&& s == if is_write {
                        MonitorState { valid: s0.valid & !d, ..s0 }
                    } else {
                        MonitorState {
                            conflicted: s0.conflicted | (pi & f & !s0.active & !s0.frozen),
                            frozen: s0.frozen | (s0.active & f),
                            ..s0
                        }
                    }
            }
        }),
    ensures
        monitor_wf(&s),
        wildcard_refines(abstraction(&s0), abstraction(&s), is_write, code),
{
    let a = abstraction(&s0);
    lemma_upto(s0, is_write, 64);
    let f = s0.valid & !pl & !s0.cell;
    let pi = s0.protected & s0.initialized;
    let d = f & !(s0.interior & !s0.active);
    assert((exists|e: nat| wild_cand(a, e, is_write)) == allowed_upto(&s0, is_write, 64)) by {
        if exists|e: nat| wild_cand(a, e, is_write) {
            let e = choose|e: nat| wild_cand(a, e, is_write);
            assert(e < 64);
        }
    }
    assert forall|i: u64| i < 64 implies {
        &&& bit(f, i) == (bit(s0.valid, i) && !bit(pl, i) && !bit(s0.cell, i))
        &&& bit(pi, i) == (bit(s0.protected, i) && bit(s0.initialized, i))
        &&& bit(d, i) == (bit(f, i) && !(bit(s0.interior, i) && !bit(s0.active, i)))
        &&& bit(s0.valid & !d, i) == (bit(s0.valid, i) && !bit(d, i))
        &&& bit(s0.conflicted | (pi & f & !s0.active & !s0.frozen), i) == (bit(s0.conflicted, i)
            || (bit(pi, i) && bit(f, i) && !bit(s0.active, i) && !bit(s0.frozen, i)))
        &&& bit(s0.frozen | (s0.active & f), i) == (bit(s0.frozen, i) || (bit(s0.active, i)
            && bit(f, i)))
        &&& bit(pl, i) == wild_local(a, i as nat, is_write)
    } by {
        lemma_bit_and(s0.valid, !pl, i);
        lemma_bit_not(pl, i);
        lemma_bit_and(s0.valid & !pl, !s0.cell, i);
        lemma_bit_not(s0.cell, i);
        lemma_bit_and(s0.protected, s0.initialized, i);
        lemma_bit_and(f, !(s0.interior & !s0.active), i);
        lemma_bit_not(s0.interior & !s0.active, i);
        lemma_bit_and(s0.interior, !s0.active, i);
        lemma_bit_not(s0.active, i);
        lemma_bit_and(s0.valid, !d, i);
        lemma_bit_not(d, i);
        lemma_bit_and(pi, f, i);
        lemma_bit_and(pi & f, !s0.active, i);
        lemma_bit_and(pi & f & !s0.active, !s0.frozen, i);
        lemma_bit_not(s0.frozen, i);
        lemma_bit_or(s0.conflicted, pi & f & !s0.active & !s0.frozen, i);
        lemma_bit_and(s0.active, f, i);
        lemma_bit_or(s0.frozen, s0.active & f, i);
    }
    if allowed_upto(&s0, is_write, 64) {
        if is_write && pi & d != 0 {
            lemma_and_nonzero(pi, d);
            let i = choose|i: u64| i < 64 && bit(pi, i) && bit(d, i);
            assert(i < s0.count) by { if i >= s0.count { assert(!bit(s0.valid, i)); } }
            assert(wild_step(a, i as nat, is_write) is None);
        } else {
            if is_write { lemma_and_nonzero(pi, d); }
            assert forall|t: nat| t < a.count implies (#[trigger] wild_step(a, t, is_write)) is Some
                && node_eq(abstraction(&s).nodes[t], wild_step(a, t, is_write)->Some_0) by {
                lemma_wild_node(s0, s, is_write, pl, t as u64);
            }
            // The permission invariants.
            assert forall|i: u64| i < 64 implies
                (bit(s.frozen, i) && bit(s.interior, i) ==> bit(s.active, i))
                && (bit(s.conflicted, i) ==> !bit(s.active, i) && !bit(s.frozen, i)
                    && bit(s.protected, i) && bit(s.initialized, i))
                && (s0.count <= i ==> !bit(s.valid, i) && !bit(s.frozen, i)
                    && !bit(s.conflicted, i)) by {
                lemma_wild_bits(s0, pl, i);
                if is_write { lemma_bit_zero(i); }
            }
            assert(s.ancestors == s0.ancestors && s.alias == s0.alias && s.cell == s0.cell);
        }
    }
}

fn main() {}

} // verus!
