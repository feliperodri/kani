# Aliasing checks

`-Z aliasing-checks` checks memory accesses against a model of Rust's aliasing rules. The model
is the part that [Stacked Borrows](https://plv.mpi-sws.org/rustbelt/stacked-borrows/paper.pdf)
and [Tree Borrows](https://research.ralfj.de/papers/2025-pldi-tree-borrows.pdf) agree on, so an
access it rejects is undefined behavior under either model. It covers fewer programs than either
model does: some aliasing violations are not reported yet (see [Limitations](#limitations)).

```rust
#[kani::proof]
fn check() {
    let mut x = 0;
    let p = &mut x as *mut i32;
    let r = unsafe { &mut *p };
    unsafe { *p = 1 }; // The write through `p` invalidates `r`...
    *r = 2;            // ...so writing through `r` is undefined behavior.
}
```

```
Failed Checks: Undefined Behavior: memory accessed through a reference or pointer whose borrow was invalidated by a conflicting access (aliasing checks)
```

## The model

Every reference that the program creates, by `&place` or `&mut place`, gets a *tag*. The tag's
parent is the tag of the pointer through which `place` is reached, or the *root* tag of the
allocation when `place` is a local variable or the contents of a `Box`. Raw pointers keep the
tag of the reference they are derived from. This is Tree Borrows' behavior, and both models
agree on the programs below.

An access through a tag is *local* to that tag and its ancestors, and *foreign* to every other
tag. Each tag is:

- *valid* until a conflicting access disables it;
- *active* once memory is written through it or through one of its descendants;
- *frozen* if it is a shared reference, or if it was active when a foreign read happened.

The rules are:

1. Creating a reference reads the memory it points to through its parent's tag.
2. Accessing memory through a tag that is not valid is undefined behavior.
3. Writing through a tag that has a frozen ancestor, or is frozen, is undefined behavior.
4. A write disables every foreign tag.
5. A read freezes every foreign tag that is active.

Rules 4 and 5 differ from each model's own rules only where the two models disagree. Stacked
Borrows also disables a mutable reference on a foreign read. Tree Borrows lets a mutable
reference that was never written (*reserved*) survive foreign reads. Kani follows Tree Borrows in
both cases, so programs that only Stacked Borrows rejects pass.

As with `-Z uninit-checks`, Kani tracks the state of one byte of memory per harness. The byte is
chosen nondeterministically, so if any byte is accessed against the rules, some execution
tracks that byte and the check fails.

## Limitations

The following are not checked yet. Accesses that depend on them pass even when they are undefined
behavior; none of them makes Kani report undefined behavior that is not there.

- **Pointers stored in memory.** A pointer read back from memory, for example a reference field
  of a struct or the buffer pointer of a `Vec`, gets a *wildcard* tag. Accesses through a
  wildcard pointer are neither checked nor change the state. This includes the pointer that
  `Vec::as_mut_ptr` returns.
- **Calls.** Tags of pointer arguments and returned pointers go through direct calls, for up to
  four arguments. Indirect calls (function pointers, `dyn`) pass wildcard tags.
- **Protectors.** Function-entry retags and protectors are not modelled, so writing through an
  alias of a `&mut` argument while the function runs is only reported if the argument is used
  afterwards.
- **`UnsafeCell`.** References to types that are not `Freeze` keep their parent's tag.
  Creating a reference to an unsized type (a slice, `str`, `dyn Trait`) does not check the read
  it performs.
- **Places with several dereferences** (`**p`), pointers obtained from integers, and memory
  accessed by intrinsics such as `copy_nonoverlapping` are not checked.
- **Deallocation** does not invalidate tags.
- Kani tracks at most 63 references to the tracked byte at once. The tags of references created
  by a function are dropped when it returns, unless it returns one. Beyond 63, a new reference
  shares the tag of the pointer it was created from, so undefined behavior through that
  reference alone is missed.

## Validation

The tests in `tests/expected/aliasing` are litmus tests that were also run under Miri with
`-Zmiri-tree-borrows` and with Stacked Borrows. Kani agrees with Miri's Tree Borrows result on
all of them except the known gaps above, which the tests mark as such.

## Status and next steps

The checks are built around tags, ancestry and an abstract permission state rather than a borrow
stack, so that Tree Borrows' permission machine can refine them instead of replacing them. They
currently cover:

- tags for references, propagated through copies, casts, pointer arithmetic and direct calls;
- parent/child ancestry, with local and foreign accesses distinguished;
- valid/invalid tags, read and write permissions, and freezing on foreign reads;
- per-byte state, since one byte is tracked (disjoint fields of a struct do not interfere).

Planned next, roughly in order: tags for pointers stored in memory, protectors for function
arguments, `UnsafeCell`, Tree Borrows' reserved and active states with their exact transitions,
deallocation, and exposed provenance.
