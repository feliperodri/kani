# WIP: Rust toolchain upgrade to `nightly-2026-05-01`

**Status: work in progress.** The upgrade builds and passes essentially the whole regression
suite, but there is one unresolved regression (`tests/cargo-kani/mir-linker`, see
[Known issue](#known-issue-mir-linker-does-not-terminate)) and one suite that was never run
(`std-checks`). Do not merge without resolving both.

This branch bumps `rust-toolchain.toml` from `nightly-2026-04-01` (the state committed on
`upgrade-toolchain-2026-05-01`) to `nightly-2026-05-01`.

---

## 1. What changed upstream

### 1.1 `NonNull<T>` now holds a pattern type

This is the root cause of most of the breakage.

```rust
// nightly-2026-04-01
pub struct NonNull<T: PointeeSized> {
    pointer: *const T,
}

// nightly-2026-05-01
pub struct NonNull<T: PointeeSized> {
    pointer: crate::pattern_type!(*const T is !null),
}
```

Kani codegens a pattern type as a struct with a single tuple-like field holding the type it
constrains (`codegen_ty`, `ty::Pat` arm). So the raw pointer behind `NonNull` moved one level
deeper, breaking five places that assumed a fixed nesting depth. Because `DynMetadata` holds a
`NonNull<VTable>`, this reached vtable/metadata codegen as well.

All fixes are written to be **depth-agnostic** rather than adding one more hop. `raw_ptr_arg`
had already broken once before on exactly this assumption (it was introduced when the
allocation shims switched from `*mut u8` to `NonNull<u8>` in nightly-2026-03-21), so hardcoding
the new depth would just defer the next break.

### 1.2 `rustc_public` lost the `ty::Alias` stable conversion

```rust
// nightly-2026-04-01 - compiler/rustc_public/src/unstable/convert/stable/ty.rs
ty::Alias(alias_kind, alias_ty) => {
    TyKind::Alias(alias_kind.stable(tables, cx), alias_ty.stable(tables, cx))
}

// nightly-2026-05-01 - the alias kind moved into `AliasTy`, conversion left unimplemented
ty::Alias(_alias_ty) => {
    todo!()
}
```

Calling the stable `Ty::kind()` on an un-normalized alias now panics. `kani-compiler` normalizes
before inspecting types (`ty::Alias(..) => unreachable!("Type should've been normalized already")`),
so it is unaffected. The `scanner` tool does not, so it ICE'd. **Worth reporting upstream.**

### 1.3 `PatternKind::NotNull` is now convertible

The inverse of the above: `PatternKind::NotNull` was `todo!()` in 04-01 and converts to
`Pattern::NotNull` in 05-01. This makes the internal-representation workaround in
`check_uninit/../check_values.rs` (`is_pattern_type`, added in 867d9385f for nightly-2026-03-01)
redundant. It is still correct, so it was left alone to keep the diff focused — **optional
follow-up cleanup**.

### 1.4 Assorted API changes

| Change | Site |
| --- | --- |
| `rustc_middle::mir::mono::CodegenUnitNameBuilder` moved to `rustc_middle::mono` | `utils/names.rs` |
| `type_of(..).instantiate*()` now returns an unnormalized wrapper; needs `.skip_normalization()` | `codegen_units.rs`, `intrinsics.rs`, `stubbing/mod.rs` |
| `tcx.has_attrs_with_path` removed; use `get_attrs_by_path(..).next().is_some()` | `check_uninit/ptr_uninit/mod.rs` |
| `test::run_tests_console` now takes a `TestList` tagged with an ordering | `tools/compiletest/src/main.rs` |

On the compiletest change: the list must be tagged `Unsorted`. compiletest collects tests by
walking directories, so it is not name-ordered, and the harness binary-searches a list tagged
`Sorted`.

---

## 2. Code changes

### Pattern-type / `NonNull` fixes

| File | Change |
| --- | --- |
| `kani_middle/coercion.rs` | Added a `RigidTy::Pat` arm to `CoerceUnsizedIterator::next` so the unsize-coercion path steps through the pattern type (field `"0"`) and the base case reaches the real pointer. |
| `codegen/rvalue.rs` | `codegen_struct_unsized_coercion` accepts pattern types via a new `is_struct_like` (ADT *or* `Pat` - both are codegen'd as assignable structs). Both `DynMetadata` sites now use the recursive helpers below instead of hardcoded `.member("pointer")` / one-level `lookup_components()[0]`. |
| `utils/utils.rs` | New `codegen_ptr_in_wrappers` (wrap a pointer in N single-field struct layers) and `codegen_ptr_out_of_wrappers` (peel them off). Inverses of each other; independent of nesting depth. |
| `codegen/typ.rs` | `receiver_data_path` walks through pattern types; `codegen_trait_receiver`'s rebuild fold handles a `Pat` path element. |
| `codegen/place.rs` | `codegen_field` projects into a pattern type (reads field `"0"`) instead of `unreachable!`. Rust itself forbids this projection, but **Kani synthesizes one** in `raw_ptr_arg`, so it must be supported. |
| `check_uninit/ptr_uninit/uninit_visitor.rs` | `raw_ptr_arg` derives its projection chain from the actual field types via a new `single_field_ty`, looping until it reaches a raw pointer, instead of pushing one hardcoded `Field(0, *const T)`. |
| `kani_middle/mod.rs` | Updated `nonnull_pointee` doc comment for the new field shape. |

### `scanner` fix (`ty::Alias` `todo!()`)

`tools/scanner/src/{lib,analysis,call_graph}.rs`: threaded `TyCtxt` down to `BodyVisitor` and
`Node::try_new` so the union check in `visit_projection_elem` uses
`rustc_internal::internal(tcx, ty).is_union()`. The internal representation is always safe to
inspect and reports an alias as not-a-union, which is exactly what the stable `TyKind::Alias`
did before it became unconvertible - so behaviour is preserved, not just the crash avoided.

---

## 3. Verification results

Run locally on macOS aarch64, CBMC 6.10.0 (`cbmc-6.9.0-214-g45436eea34`).

| Suite | Mode | Result |
| --- | --- | --- |
| `kani` | kani | **600 passed, 0 failed**, 23 ignored |
| `expected` | expected | **466 passed, 0 failed**, 15 fixme/ignore (481 total) |
| `ui` | expected | 142 passed, **2 failed** - both are the `cadical` tests, see [env](#5-environment-caveats) |
| `cargo-kani` | cargo-kani | **70/71**; `mir-linker` never finishes, see [known issue](#known-issue-mir-linker-does-not-terminate) |
| `cargo-ui` | cargo-kani | 30 passed, 0 failed |
| `script-based-pre` | exec | 53 passed, 0 failed, 1 ignored |
| `prusti` | kani | 8 passed |
| `smack` | kani | 40 passed |
| `firecracker` | kani | 0 passed, 2 ignored |
| `kani-fixme` | kani-fixme | 22 passed, 601 ignored |
| `coverage` | coverage-based | 20 passed |
| `cargo-coverage` | cargo-coverage | 2 passed |
| `kani-docs` | cargo-kani | 13 passed |
| `json-handler` | exec | 5 passed |
| `std-checks` | cargo-kani | **NOT RUN** - see [gaps](#4-gaps) |

Other gates, all clean:

- `cargo build-dev`
- `cargo build-dev -- --features cprover --features llbc` (genuinely recompiled `charon v0.1.91`)
- `cargo clippy --workspace --tests -- -D warnings`
- `RUSTFLAGS="--cfg=kani_sysroot" cargo clippy --workspace -- -D warnings`
- `./scripts/kani-fmt.sh --check`
- Unit tests: `cprover_bindings`, `kani-compiler`, `kani-driver`, `kani_metadata`,
  `kani --features concrete_playback`, `kani_macros`

The dedicated `RUSTFLAGS="-D warnings" cargo build --no-default-features --features cprover`
step from `kani-regression.sh` was not run separately (no disk headroom, see gaps); the two
clippy `-D warnings` runs above cover the same ground.

---

## Known issue: `mir-linker` does not terminate

`tests/cargo-kani/mir-linker` verifies a `semver::Version` comparison. Measured against the
committed 04-01 baseline (built by stashing this work, so same Kani code except the toolchain):

| | `nightly-2026-04-01` | `nightly-2026-05-01` |
| --- | --- | --- |
| Result | SUCCESS in **4.4 s** | does not terminate |
| Checks | 827 | 827 (with `--default-unwind 4`) |
| Loops unwound | 1 (`BuildMetadata::cmp`) | 5000+ (`memchr_naive`, `decode_len_cold`) |

**The property itself is fine.** With `--default-unwind 4 --no-unwinding-checks` it is
`0 of 827 failed`, `VERIFICATION:- SUCCESSFUL` - the same 827 checks as the baseline, so the
goto model is the same size.

### Mechanism

`semver`'s `Identifier` is a tagged pointer: `Identifier::empty()` stores the sentinel
`NonNull::new_unchecked(!0 as *mut u8)`, and `as_str()` branches on
`is_empty()` / `is_inline()` before treating the pointer as a heap allocation. On 05-01 CBMC no
longer folds the `is_empty()` guard during symbolic execution, so symex explores the
**infeasible** heap-representation branch, whose `decode_len_cold` varint loop is unbounded -
hence non-termination. The solver ultimately proves that branch infeasible (values are correct);
symex just never gets there.

### Ruled out (verified, do not re-investigate)

- **Not the solver.** Initially misdiagnosed as the missing `cadical`; it is a symex explosion.
- **Not the pattern-type goto model.** Modelling `ty::Pat` transparently
  (`ty::Pat(base_ty, ..) => self.codegen_ty(*base_ty)`, which restores the exact 04-01
  `NonNull` goto shape `struct { pointer: *const T }`) **does not fix it** - still 5000+
  unwindings. That experiment was implemented and reverted; the wrapper model is what ships.
- **Not `NonNull::as_ptr`.** Byte-identical in both toolchains (`mem::transmute::<Self, *mut T>`).
- **Not const codegen.** Targeted harnesses pass on 05-01: sentinel round-trip
  (`as_ptr() as usize == !0`), nondeterministic round-trip, `const NonNull` value, two reads of
  the same const comparing equal, and a const struct `{ head: NonNull, tail: [u8; 8] }`
  self-comparing.

### Remaining suspect

How the pattern type affects the **MIR** feeding that guard - e.g. whether
`Prerelease::EMPTY` is now materialised as a promoted static read rather than an immediate, or
whether the `transmute` in `as_ptr` gains a step. Next probe: dump and diff MIR for
`NonNull::as_ptr` / `Identifier::is_empty` across the two toolchains (needs dependency MIR, so
`-Zdump-mir` on a crate that inlines them), and diff the generated goto model around the guard.

### Reproduce

```bash
cd tests/cargo-kani/mir-linker
cargo kani                                          # hangs, unwinding memchr_naive
cargo kani --default-unwind 4 --no-unwinding-checks  # 0 of 827 failed, SUCCESSFUL
```

---

## 4. Gaps

- **`std-checks` was never run.** The disk filled to 100% mid-session; ~17 GB of gitignored
  build caches were reclaimed (`target/debug/incremental`, `target/release`, stale
  `tests/**/target`, `tests/**/*.out`) to make progress. `std-checks` builds all of `std` and
  needs real headroom. **This is the one untested suite.**
- **`cargo-kani` is 70/71**, blocked only by `mir-linker`.

---

## 5. Environment caveats

The local CBMC build has **no `cadical`**; every test requesting it silently falls back to
MiniSat (`"The specified solver, 'cadical', is not available. The default solver will be used
instead."`). This is not a code problem, but it distorts local results:

- `ui/solver-attribute/cadical` and `ui/solver-option/cadical` fail because they expect the
  literal output `Solving with CaDiCaL`. These are the only two `ui` failures.
- `expected/shadow/slices/slice_split` **passes but takes ~79 minutes** under MiniSat.

Both are expected to be clean on CI, whose CBMC includes `cadical`.

Two useful flags when re-running locally:

- `--no-fail-fast` - compiletest otherwise stops at the first failure, which hides the rest.
- `--force-rerun` - compiletest caches passes and reports them as `ignored` on a re-run, so a
  plain re-run can look misleadingly small.

If you delete `tests/**/*.out` to reclaim space, also delete the per-test `tests/**/target`
directories (at **any** depth, e.g. `cargo_manifest_test/add/target`). Otherwise cargo considers
those crates fresh, never regenerates the deleted `.symtab.out`, and ~15 cargo-based tests fail
with `No such file or directory (os error 2)`.

---

## 6. Housekeeping

- The **`charon` submodule has uncommitted local modifications that predate this work**
  (file mtimes 12:57 vs the first toolchain commit at 17:59 the same day). They reverse the
  `annotate-snippets` 0.11.5 API back to 0.11.4 and set `edition = "2024"`. They are *not* part
  of this upgrade and are deliberately not committed here - but they will follow you into any
  future commit if left dirty. Decide separately whether to keep or discard them.
- `CLAUDE.md` in the repo root is untracked and also predates this work; left alone.
