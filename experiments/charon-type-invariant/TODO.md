# What Kani's Charon (LLBC) front end needs for this to work without upstream Charon

Found while running `slots.rs` through `kani -Zlean` and Aeneas. Ordered by how much each one
blocks.

1. **Translate pre-optimization MIR.** The backend reads optimized MIR (`fndef.body()`), where
   rustc turns moves into copies (`Option::Some { _0: copy x }` for `x: T`) and has no drops left.
   Aeneas tracks ownership, and fails on `push` with an internal error. Upstream Charon reads MIR
   before optimizations (`_8 = move x`, explicit `conditional_drop`s). Needs a way to get
   borrow-checked MIR from inside Kani's driver (as Charon does by overriding the MIR queries), or
   a `rustc_public` API for it. This is the bulk of the work.
2. **Calls to generic functions from generic bodies.** `Option<T>::is_none()` or
   `core::mem::size_of::<T>()` inside a generic function crash in `translate_fn_ptr`
   (`rustc_public_bridge` panics: "needs further instantiation"). Call operands are typed with
   the monomorphized body (`func.ty(self.instance.body()...)`, `mir_to_ullbc/mod.rs`), then
   resolved as an `Instance`. They should be typed with the generic body and translated as a
   `FnDef` with generic arguments, without resolving an instance.
3. **Drops of generic values.** Dropping an `Option<T>` (e.g. `let S { a, b: _ } = s;`) reaches
   `drop_in_place::<Option<T>>` and crashes the same way. Charon emits `conditional_drop` with
   the type's `Destruct` impl; the backend has no equivalent for generic types.
4. **Discriminant reads of non-ADT places** (`todo!` in `translate_rvalue`) were hit through the
   wrong place type; fixed by item 7, but the `todo!` should become a reported error.
5. **Output naming.** Kani writes `<crate>__<mangled harness>.symtab.llbc`, so Aeneas names the
   Lean module `GenRNvCs…symtab`. Emit one file per crate with a plain name, or take a
   `--dest-file`.
6. **What gets translated.** `-Zlean` translates what a harness reaches. A generic proof wants
   the crate's public generic items (Kani has `ReachabilityType::PubFns`); check that it works
   with `-Zlean`, so a library can be translated without a dummy harness.
7. **Done on this branch (822a934f1):** the crate now records Charon's options (Aeneas rejected
   every Kani file for lacking `--preset=aeneas`), and place, rvalue and discriminant types come
   from the generic body being translated, with projections (tuples and `&mut self` matches were
   typed with the `u32` instance).
8. **Version coupling with Aeneas.** Aeneas accepts only LLBC from the exact Charon version it
   pins. `charon-update.yml` picks the latest Charon tag; for this pipeline it should pick the
   Charon commit pinned by an Aeneas release (here, 0.1.286 ↔ `nightly-2026.10.14-bbc0151`).
9. **Connect the two halves.** `is_valid` (Rust, for Kani) and `Slots.inv` (Lean) are written
   twice by hand, and nothing checks that they agree. Options: generate one from the other, or
   let Kani use the Lean theorems as trusted contracts (e.g. `#[kani::ensures(is_valid(&result.0))]`
   on `push`, with `stub_verified`-style use in callers), so callers' harnesses rely on the
   proof instead of re-checking `push` per type.
10. **Check why a function named `none` fails Aeneas's name registration** with Kani's LLBC
    (`Error when registering the name for id: none::none`), and whether upstream Charon's
    output has the same problem.

Environment notes (not Kani bugs): prebuilt Charon and Lean's bundled `clang` need glibc ≥ 2.29,
and this host has 2.26. Charon was built from source, and Lake runs in a Debian container.
