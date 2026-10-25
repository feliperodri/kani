# Verus proof of the aliasing monitor

`aliasing_monitor.rs` proves that the transition core of Kani's aliasing checks
(`kani_aliasing_monitor!` in `../src/aliasing_monitor.rs`) implements Tree Borrows' rules at one
memory location, as Miri implements them (`miri/src/borrow_tracker/tree_borrows`) and as this file
restates them.

The proof is about the code Kani runs. This crate includes `../src/aliasing_monitor.rs` and
expands the macro, so Verus verifies the same functions Kani compiles into its library. Their
specifications and proof calls are attributes and statements behind `cfg(verus_keep_ghost)`,
which only Verus sets; Kani's build ignores them.

## Running

With Verus 0.2026.10.18:

```
verus library/kani_core/verus/aliasing_monitor.rs
```

Expected: `verification results:: 118 verified, 0 errors`. The proof uses no `assume`, `admit` or
`external_body`.

## What is proved

The abstract state (`AbsState`) is the set of trees of tags at the tracked location: the
allocation's tree, rooted at tag 0, and the wildcard trees that references created from pointers
with exposed provenance start. Each tag has its ancestors, a Tree Borrows permission (Reserved,
possibly conflicted or interior-mutable; Active; Frozen; Disabled), and whether it is protected
(strongly or weakly), initialized at the location (Miri's "accessed"), exposed, or a shared
reference to the bytes of an `UnsafeCell` (Miri's `Cell`, which acts through `alias`).
`abstraction` maps the monitor's bit sets to it; `monitor_wf` is the invariant every function
preserves.

The transitions are Miri's `perms.rs` (`local_step` / `foreign_step`, with `ProtectedDisabled`).
Every access goes through one function, `monitor_apply`, proved to apply `local_step` to the tags
of its local set, `foreign_step` to those of its foreign set, and nothing to the others, with
undefined behavior exactly when one of these transitions is. The other functions are proved to
compute the sets that Miri's rules give.

| Function | Theorem (ensures) | Plan stage |
|---|---|---|
| `monitor_initialize` | one root tag, Active and initialized (`initial_spec`) | 0 |
| `monitor_new_borrow` | `retag_spec`: a child of `parent`, or the root of a wildcard tree, with Miri's `NewPermission` (inside and outside the range; protected references are never interior-mutable) | 0, 1, 7, 8, 9, 11 |
| `monitor_apply` | `apply_refines`: the transitions of an access, given its local and foreign tags | 2-7, 9 |
| `monitor_access` | `access_refines`: the access through a tag; from a wildcard tree, also Miri's wildcard access to the other trees | 2-7, 9, 11 |
| `monitor_wildcard_access` | `wildcard_refines`: Miri's `perform_wildcard_access` on every tree (`wild_access`) | 11 |
| `monitor_dealloc` | `dealloc_refines`: a write through the pointer, then `ProtectedDealloc` for strong protectors | 10 |
| `monitor_end_protector` | `end_protector_refines`: Miri's `perform_protector_end_access`, skipping the wildcard trees that may hang below the tag (`min_exposed_child`) | 9 |
| `monitor_expose` | `expose_spec`: the tag accesses act through becomes exposed | 11 |
| `monitor_store` | `store_spec`: the tag of a pointer stored in memory is recorded, so that the frame that created it keeps it | 11 |
| `monitor_return` | `return_spec`: protectors end; unexposed tags of the frame that are not returned are dropped | 9 |

All of them also preserve `monitor_wf`. Results the checks cannot decide
(`ACCESS_UNKNOWN_*`) carry no theorem beyond `monitor_wf`; the library reports them as
unsupported.

## Mutation check

`exp/alias/verus/mutants.py` (outside the repository) applies one-line bugs to the monitor; the
proof must reject each of them.

## What is not proved (trusted)

- That the specification (`local_step`, `foreign_step`, `retag_node`, `wild_access`, ...) states
  Miri's Tree Borrows correctly. It is a transcription of Miri's code, cited in the comments, and
  is checked against Miri by running Miri's own borrow tests under both tools. The first version
  of this specification had four rules wrong, which only that comparison found.
- The wrappers in `aliasing.rs` (pointer to object/offset, coverage of the tracked byte,
  `UnsafeCell` byte masks, passing tags across calls) and the compiler instrumentation in
  `kani-compiler/src/kani_middle/transform/check_aliasing.rs`.
- That dropping the tags of a returning function is sound: it relies on the instrumentation
  recording, with `monitor_store`, every tag it stores in shadow memory, and giving the other
  pointers read from memory the unknown tag.
- Verus, its Z3 back end, and the arithmetic semantics they assume for the monitor's `u64`/`u8`
  operations, which Kani executes through CBMC.
