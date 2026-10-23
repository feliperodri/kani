# Aliasing checks

`-Z aliasing-checks` checks memory accesses against a model of Rust's aliasing rules. The model
is the part that [Stacked Borrows](https://plv.mpi-sws.org/rustbelt/stacked-borrows/paper.pdf)
and [Tree Borrows](https://research.ralfj.de/papers/2025-pldi-tree-borrows.pdf) agree on, so an
access it rejects is undefined behavior under either model. Some rules of those models are not
checked yet; see [What a successful verification means](#what-a-successful-verification-means).

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
6. When a function starts, each of its reference arguments is reborrowed, and the new tag is
   *protected* until the function returns. While it is protected, a write that would disable it
   is undefined behavior, and so is writing through it after a foreign read if it had not been
   written before. As in Tree Borrows, this only applies to memory in the range of the reference
   or accessed through it.
7. The bytes of an `UnsafeCell` behind a shared reference are not frozen: a shared reference to
   them acts like the pointer it was created from, and writes through it are allowed. A mutable
   reference to them is not disabled by foreign writes until it is written.

Rules 4 and 5 differ from each model's own rules only where the two models disagree. Stacked
Borrows also disables a mutable reference on a foreign read. Tree Borrows lets a mutable
reference that was never written (*reserved*) survive foreign reads. Kani follows Tree Borrows in
both cases, so programs that only Stacked Borrows rejects pass.

As with `-Z uninit-checks`, Kani tracks the state of one byte of memory per harness. The byte is
chosen nondeterministically, so if any byte is accessed against the rules, some execution
tracks that byte and the check fails.

## What a successful verification means

If a harness verifies with `-Z aliasing-checks`, no execution of the harness breaks rules 1 to 7
above. Kani never reports success because of an access it did not check. When it cannot tell
which tag a pointer has, it gives the pointer an *unknown* tag. An access through an unknown tag
to the tracked byte then fails with "Kani's aliasing checks do not know which reference this
pointer was derived from". That failure is inconclusive, not a proof of undefined behavior.
Today the tag is unknown for:

- pointers read back from memory (a reference stored in a struct field, the buffer pointer of a
  `Vec`), except the pointer inside a `Box`;
- places that go through a pointer stored in memory, such as `**p`;
- pointers returned by, or passed as arguments to, indirect calls (function pointers, `dyn`),
  and pointer arguments past the fourth;
- pointers obtained from integers;
- pointer locals whose own address is taken;
- shared references to types whose `UnsafeCell` bytes the checks cannot locate: an enum or a
  union that contains an `UnsafeCell`, an `UnsafeCell` past the first 64 bytes, or an unsized
  type that contains one;
- references created after 63 references to the tracked byte are live. The tags of references
  a function creates are dropped when it returns, unless it returns one.

SIMD gather, scatter and masked load/store intrinsics are reported as unsupported.

### Rules that are not checked

Rules 1 to 7 are the whole property. The following rules of Stacked Borrows and Tree Borrows are
not part of it yet, so a successful verification says nothing about them:

- **Deallocation** while a reference to the memory is live. Kani's pointer checks still report
  accesses to deallocated memory.

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
