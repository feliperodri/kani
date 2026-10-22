# Experiment: prove a type invariant for all `T` with Charon, check instances with Kani

Theory: prove a property of generic Rust code once, for every `T`, through the Charon front end
(Charon → LLBC → Aeneas → Lean), and check the same property on monomorphized instances with
Kani's standard (CBMC) front end.

Result: it works for this example, with upstream Charon standing in for Kani's own Charon
front end, which can't produce LLBC that Aeneas accepts yet (see [TODO.md](TODO.md)).

- `slots.rs`: `Slots<T>`, at most two values of any `T`, with `new`, `push` and `pop`. Type
  invariant: `len` is the number of occupied slots, and slot `b` is occupied only if `a` is.
- `proof/Slots.lean`: the Lean model Aeneas generates from Charon's LLBC. It is parametric in `T`.
- `proof/SlotsProof.lean`: `new_spec`, `push_spec`, `pop_spec`. For every `T`, `new` establishes
  the invariant, `push` and `pop` preserve it and never overflow or underflow `len` (checked
  arithmetic is in the `Result` monad), `push` rejects a value exactly when both slots are full,
  and `pop` returns a value exactly when the slots are not empty. The proofs use only Lean's
  standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
- The Kani harnesses in `slots.rs` (`#[cfg(kani)]`) check the same invariant, plus that `pop`
  returns what `push` stored, for `u8`, `u64`, `char`, `(u16, bool)`, `[i32; 3]`, `Option<u32>`
  and `String`: 7 of 7 verify.
- Mutation check: making `push` increment `len` even when both slots are full fails `push_spec`
  in Lean and `check_u8` / `check_string` in Kani.

## Reproducing (this machine)

Versions: Kani at this branch, Charon v0.1.286 (Kani's `charon` submodule), Aeneas nightly
`nightly-2026.10.14-bbc0151` (the release pinned to Charon v0.1.286), Lean `v4.35.0-rc4`.

```sh
# Upstream Charon, built from Kani's submodule (needs `git submodule update --init --recursive`
# inside charon/ and the nightly-2026-09-17 toolchain).
(cd charon/charon && cargo build --release --bins)
C=charon/charon/target/release
PATH=$C:$PATH $C/charon rustc --preset=aeneas --dest-file slots.llbc -- \
  --crate-type=lib --edition=2021 experiments/charon-type-invariant/slots.rs
aeneas -backend lean slots.llbc -dest proof/        # writes proof/Slots.lean

# Lean: this host has glibc 2.26, so Lake runs in a Debian container (`lean-docker`).
(cd <aeneas>/backends/lean && lean-docker lake exe cache get && lean-docker lake build Aeneas)
(cd experiments/charon-type-invariant/proof && lean-docker lake build)

# Kani, standard front end
kani experiments/charon-type-invariant/slots.rs
```
