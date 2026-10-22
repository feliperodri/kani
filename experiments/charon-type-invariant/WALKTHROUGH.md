# Walkthrough: one proof for every `T`, then checks on concrete types

This is a small experiment for the question in
[verify-rust-std#734](https://github.com/model-checking/verify-rust-std/issues/734): what can it
mean to verify Rust code "for generic type `T` (no monomorphization)"? Kani checks one concrete
instantiation per harness. This experiment tries a different split:

1. **Prove the property once, for every `T`**, by translating the generic Rust code to Lean
   through Charon and Aeneas, and proving it there.
2. **Check the same property on concrete types with Kani**, which runs the real compiled code
   (all of rustc's lowering, checked arithmetic, layout) and catches undefined behaviour.

It works for the example below. It also makes clear what this route needs before it could apply
to the std challenges; see [What this does not show](#what-this-does-not-show).

Everything is in this directory: `slots.rs` (the Rust code and the Kani harnesses),
`proof/` (the generated Lean model and the proof), `TODO.md` (what Kani's own Charon front end is
missing), and `README.md` (a short summary).

## The example

```rust
pub struct Slots<T> {
    pub a: Option<T>,
    pub b: Option<T>,
    pub len: u8,
}
```

A container for at most two values of any type `T`, with `new`, `push` (store in the first free
slot, or give the value back if both are full) and `pop` (remove the most recent value). Its type
invariant:

1. `len` is the number of occupied slots, and
2. slot `b` is occupied only if slot `a` is.

`push` and `pop` change `len` with checked arithmetic (`len + 1`, `len - 1`), so a broken
invariant would show up as an overflow or underflow panic, not just a wrong count.

The functions only move values: no calls to generic methods such as `Option::is_none`, and no
drops of `T`. That keeps them inside what this pipeline handles today (see `TODO.md`); it is a
limitation of the tools, not of the approach.

## Step 1: Rust → LLBC with Charon

[Charon](https://github.com/AeneasVerif/charon) reads rustc's MIR and produces LLBC, a structured
form of it, without monomorphizing. The `push` it produces is still generic:

```
pub fn push<T>(s: Slots<T>, x: T) -> (Slots<T>, Option<T>)
```

```sh
charon rustc --preset=aeneas --dest-file slots.llbc -- --crate-type=lib --edition=2021 slots.rs
```

Kani has its own Charon front end (`kani -Zlean`), which emits LLBC from inside Kani's compiler.
I tried it first. It translates generic functions generically too, but its output is not yet
accepted by Aeneas (mainly because it reads MIR after rustc's optimizations; see `TODO.md`). So
this experiment uses upstream Charon, built from Kani's `charon` submodule (the same Charon
version), for this step. Making Kani's front end good enough to replace it is the follow-up.

## Step 2: LLBC → Lean with Aeneas

[Aeneas](https://github.com/AeneasVerif/aeneas) turns LLBC into a pure functional model. Panics
and overflow become a `Result`. `proof/Slots.lean` is its output, unedited:

```lean
def push
  {T : Type} (s : Slots T) (x : T) : Result ((Slots T) × (Option T)) := do
  match s.a with
  | none =>
    let i ← s.len + 1#u8
    ok ({ s with a := (some x), len := i }, none)
  | some _ =>
    match s.b with
    | none =>
      let i ← s.len + 1#u8
      ok ({ a := s.a, b := (some x), len := i }, none)
    | some _ => ok (s, some x)
```

`s.len + 1#u8` is checked addition: it fails if `len` is 255. `T` is a type parameter of the
model, so anything proved about `push` holds for every `T`.

```sh
aeneas -backend lean slots.llbc -dest proof/
```

## Step 3: the proof, in Lean

`proof/SlotsProof.lean` states the invariant and proves three theorems:

```lean
def Slots.count {T : Type} (s : Slots T) : Nat :=
  (if s.a.isSome then 1 else 0) + (if s.b.isSome then 1 else 0)

def Slots.inv {T : Type} (s : Slots T) : Prop :=
  s.len.val = s.count ∧ (s.b.isSome → s.a.isSome)

theorem new_spec (T : Type) : new T ⦃ s => s.inv ⦄
theorem push_spec {T : Type} (s : Slots T) (x : T) (h : s.inv) :
    push s x ⦃ r => r.1.inv ∧ (r.2.isSome ↔ s.b.isSome) ⦄
theorem pop_spec {T : Type} (s : Slots T) (h : s.inv) :
    pop s ⦃ r => r.1.inv ∧ (r.2.isSome ↔ s.a.isSome) ⦄
```

`f ⦃ r => P r ⦄` means `f` returns `ok r` (no panic, no overflow) and `P r` holds. So, for every
`T`: `new` establishes the invariant; `push` preserves it, never overflows, and rejects a value
exactly when both slots are full; `pop` preserves it, never underflows, and returns a value
exactly when the container is not empty.

Each proof is a case split on the two slots plus Aeneas's `step` tactic for the arithmetic, about
three lines. `#print axioms` shows only Lean's standard axioms (`propext`, `Classical.choice`,
`Quot.sound`), so there is no `sorry` anywhere.

```sh
cd proof && lake build
```

## Step 4: concrete types with Kani's standard front end

The harnesses in `slots.rs` (behind `#[cfg(kani)]`) check the same invariant with Kani's usual
CBMC back end. Each one starts from an arbitrary valid `Slots<T>`, pushes an arbitrary value, pops,
and checks the invariant after each step and that `pop` returns what `push` stored. They run for
`u8`, `u64`, `char`, `(u16, bool)`, `[i32; 3]`, `Option<u32>` and `String`:

```
$ kani slots.rs
Complete - 7 successfully verified harnesses, 0 failures, 7 total.
```

The invariant is written twice, as `is_valid` in Rust and `Slots.inv` in Lean. Nothing checks
that they agree; that is the first thing to fix (see `TODO.md`, item 9).

## Step 5: do both halves catch a bug?

A test that cannot fail tells you nothing, so I broke `push`: when both slots are full it now
increments `len` anyway.

```rust
Some(vb) => (Slots { a: Some(va), b: Some(vb), len: len + 1 }, Some(x)),
```

After rerunning Charon and Aeneas on the broken code, `push_spec` no longer proves
(`unsolved goals`). Kani's `check_u8` and `check_string` fail with
`assertion failed: is_valid(&s)`.

## What this does not show

The example is safe Rust with no trait bounds. The std challenges in #734 are mostly the opposite,
and that matters more than anything above:

- **Unsafe code.** Aeneas works on safe Rust: it models ownership and borrows, not raw pointers.
  `RawVec`, `Vec` and `LinkedList` are built on raw pointers, so this route does not reach them as
  they are. For those, the useful split is probably the one in
  [this comment](https://github.com/model-checking/verify-rust-std/issues/734#issuecomment-6331645128):
  check the layout-dependent core with Kani for every layout, and argue separately that the
  generic wrapper passes the right one.
- **Trait bounds.** With `T: Clone` or `T: Drop`, a proof for every `T` holds only relative to
  what is assumed about the trait methods. Each concrete impl then has to be checked against those
  assumptions; this example has none.
- **Two programs.** Charon reads MIR before rustc's optimizations, Kani reads it after. They are
  compilations of the same source and agree as long as rustc's optimizations are correct and the
  program has no undefined behaviour (which Kani checks on the instances it runs). That is fine for
  this split, but it is an assumption, not a proof.
- **Drops and generic calls.** The example avoids both because the pipeline crashes on them
  today (`TODO.md`, items 2 and 3).

## Reproducing it

Versions: Kani at this branch, Charon v0.1.286 (Kani's `charon` submodule), Aeneas
`nightly-2026.10.14-bbc0151` (the Aeneas release pinned to Charon v0.1.286; Aeneas only accepts
LLBC from the exact Charon version it pins), Lean `v4.35.0-rc4`.

```sh
# 1. Charon, from Kani's submodule (needs the nightly-2026-09-17 toolchain).
git -C charon submodule update --init --recursive
(cd charon/charon && cargo build --release --bins)
C=$PWD/charon/charon/target/release
cd experiments/charon-type-invariant
PATH=$C:$PATH $C/charon rustc --preset=aeneas --dest-file slots.llbc -- \
  --crate-type=lib --edition=2021 slots.rs

# 2. Aeneas: download aeneas-linux-x86_64.tar.gz from the release above.
aeneas -backend lean slots.llbc -dest proof/

# 3. Lean: the Aeneas Lean library from the same release (backends/lean in the tarball, plus
#    lean-build-aeneas-*.tar.gz unpacked into backends/lean/.lake/build), and Mathlib's cache.
(cd <aeneas>/backends/lean && lake exe cache get)
# Point proof/lakefile.lean's `require aeneas from` at <aeneas>/backends/lean, then:
(cd proof && lake build)

# 4. Kani.
kani slots.rs
```

On a host with an old glibc (this was run on glibc 2.26), prebuilt Charon and the `clang` that
Lake uses need glibc ≥ 2.29: build Charon from source, and run Lake in a container.
