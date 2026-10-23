# Verus proof of the aliasing monitor

`aliasing_monitor.rs` proves that the transition core of Kani's aliasing checks
(`kani_aliasing_monitor!` in `../src/aliasing_monitor.rs`) implements the rules it documents:
Tree Borrows' transitions at one memory location, as restated in this file.

The proof is about the code Kani runs. This crate includes `../src/aliasing_monitor.rs` and
expands the macro, so Verus verifies the same functions Kani compiles into its library. Their
specifications and proof calls are attributes and statements behind `cfg(verus_keep_ghost)`,
which only Verus sets; Kani's build ignores them.

## Running

With Verus 0.2026.10.18:

```
verus library/kani_core/verus/aliasing_monitor.rs
```

Expected: `verification results:: 70 verified, 0 errors`. The proof uses no `assume`, `admit` or
`external_body`.

## What is proved

The abstract state (`AbsState`) is the tree of tags at the tracked location: each tag has its
ancestors, a Tree Borrows permission (Reserved, possibly conflicted or interior-mutable; Active;
Frozen; Disabled), and whether it is protected, initialized at the location, exposed, or a shared
reference to the bytes of an `UnsafeCell` (which acts through `alias`). `abstraction` maps the
monitor's bit sets to it; `monitor_wf` is the invariant every function preserves (the ancestors of
each tag form a chain to the root, aliases point at an ancestor that is a node, nothing is recorded
above `count`, and three permission invariants).

| Function | Theorem (ensures) | Plan stage |
|---|---|---|
| `monitor_initialize` | one root tag, Active and initialized (`initial_spec`) | 0 |
| `monitor_new_borrow` | `retag_spec`: a child of `parent` with the permission of a new `&mut` (Reserved, interior-mutable at cell bytes) or `&` (Frozen; no node at cell bytes), protected for function arguments; other tags unchanged | 0, 1, 7, 8, 9 |
| `monitor_access` | `access_refines`: returns `ACCESS_OK` exactly when no tag's Tree Borrows transition (`local_step` / `foreign_step`) is undefined behavior, and then every tag's new node is that transition | 2-7, 9 |
| `monitor_dealloc` | UB exactly when a protected tag has an initialized permission that is not Disabled (`dealloc_ub`) | 10 |
| `monitor_expose` | `expose_spec`: the tag accesses act through becomes exposed | 11 |
| `monitor_wildcard_access` | `wildcard_refines`: UB exactly when no exposed tag allows the access; otherwise only tags foreign to every allowing exposed tag take the foreign transition | 11 |
| `monitor_return` | `return_spec`: the returning function's tags stop being protected; tags above the kept count are dropped | 9 |

All of them also preserve `monitor_wf`.

## Mutation check

`exp/alias/verus/mutants.py` (outside the repository) applies 16 one-line bugs to the monitor,
including reverting each soundness fix found while writing this proof; the proof rejects all 16.

## What is not proved (trusted)

- That `local_step`, `foreign_step` and the rest of the specification state Tree Borrows
  correctly: they are a transcription of the paper's rules, checked against Miri by the litmus
  tests in `tests/expected/aliasing`.
- The wrappers in `aliasing.rs` (pointer to object/offset, coverage of the tracked byte,
  `UnsafeCell` byte masks, passing tags across calls) and the compiler instrumentation in
  `kani-compiler/src/kani_middle/transform/check_aliasing.rs`.
- That dropping the tags of a returning function is sound: it relies on the instrumentation
  giving pointers read from memory the unknown tag.
- Verus, its Z3 back end, and the arithmetic semantics they assume for the monitor's `u64`/`u8`
  operations, which Kani executes through CBMC.
