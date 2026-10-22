# What Kani's Charon (LLBC) front end needs for this to work without upstream Charon

Found while running `slots.rs` through `kani -Zlean` and Aeneas. Ordered by how much each one
blocks.

1. **Translate pre-optimization MIR.** The backend reads optimized MIR (`fndef.body()`), where
   rustc turns moves into copies (`Option::Some { _0: copy x }` for `x: T`) and has no drops left.
   Aeneas tracks ownership, and fails on `push` with an internal error. Upstream Charon reads MIR
   before optimizations (`_8 = move x`, explicit `conditional_drop`s). This is the bulk of the work.

   Plan, all of it gated on `-Zlean` so the CBMC path is unchanged (one backend runs per
   invocation):
   - Do what Charon does (`charon-driver/driver.rs`, `translate/get_mir.rs`): set
     `mir_opt_level = 0` and `mir_preserve_ub = true` for LLBC runs, and read
     `tcx.mir_promoted` / `tcx.mir_drops_elaborated_and_const_checked` for local items, falling
     back to optimized MIR for other crates (only optimized MIR is in their metadata).
   - rustc steals those bodies before a codegen backend runs. Either translate in an earlier
     callback, or install a query override (Kani already has `Callbacks::config`) that keeps a
     copy of each local body. Charon's driver has the override sketched as a TODO.
   - Handle what pre-optimization MIR contains: `Operand::RuntimeChecks` (with
     `-Zmir-opt-level=0` alone, `push` hits the `todo!()` in `translate_operand`), explicit
     drops, and generic calls (items 2 and 3).

   Soundness: the CBMC path does not change. For the LLBC path, pre-optimization MIR is the
   borrow-checked program; optimized MIR may have had code removed under the assumption that the
   program has no undefined behaviour (hence Charon's `mir_preserve_ub`), so the change makes that
   path more faithful. The two paths then read different MIR of the same source. That is fine for
   "prove for all T, check instances with Kani", and would also be the assumption if Kani ever
   trusted the Lean theorems as contracts (item 9): rustc's optimizations are correct and the
   program has no undefined behaviour, which Kani checks on the instances it runs.
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

11. **Uses of `const` items** produce LLBC that Charon and Aeneas reject: the backend refers to
    the global without declaring it. At `-Zmir-opt-level=0` more constants stay unevaluated, so
    this comes up more often. Tracked in
    [#5046](https://github.com/model-checking/kani/issues/5046).

Progress: items 1–3 are addressed in [#5045](https://github.com/model-checking/kani/pull/5045)
(LLBC runs compile at `-Zmir-opt-level=0`, generic calls and drops are typed with the generic
body; trait methods on generic types still need trait references). All of this work is in the
[Charon front end milestone](https://github.com/model-checking/kani/milestone/34).

Filed as issues in the milestone: trait bounds and trait method calls on generic types
([#5047](https://github.com/model-checking/kani/issues/5047)), promoted MIR for models without
drop flags ([#5048](https://github.com/model-checking/kani/issues/5048)), output naming (item 5,
[#5049](https://github.com/model-checking/kani/issues/5049)), translating without a harness
(item 6, [#5050](https://github.com/model-checking/kani/issues/5050)), the Aeneas version pin
(item 8, [#5051](https://github.com/model-checking/kani/issues/5051)), and connecting the Rust
and Lean invariants (item 9, [#5052](https://github.com/model-checking/kani/issues/5052)). Item 10
is not a Kani bug: upstream Charon's output for a function named `none` fails in Aeneas the same
way.

Environment notes (not Kani bugs): prebuilt Charon and Lean's bundled `clang` need glibc ≥ 2.29,
and this host has 2.26. Charon was built from source, and Lake runs in a Debian container.
