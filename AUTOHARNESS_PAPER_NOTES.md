# Autoharness — Research Notes

Working notes for an academic paper on Kani's **automatic harness generation**
(`kani autoharness`). This is a living document: it is updated as PRs merge and
issues are resolved. It is *not* checked into the Kani repo — it is a personal
research artifact.

- **Milestone:** [Autoharness (#33)](https://github.com/model-checking/kani/milestone/33)
- **Tracking issue:** [#3832](https://github.com/model-checking/kani/issues/3832)
- **User docs:** `docs/src/reference/experimental/autoharness.md`
- **Last updated:** 2026-08-19 (compiled from `main` + open PR series)

> Maintenance: when a PR from the series below merges, move it to
> [§8 Changelog](#8-changelog), update the affected capability in [§4](#4-capabilities-and-limitations),
> and fold any new evaluation numbers into [§6](#6-evaluation-data-cratesio-corpus).

---

## 1. Problem statement and thesis

Most Kani proof harnesses are boilerplate: to verify `fn foo(x: A, y: B)`, the
user writes a harness that creates `kani::any()` values for each argument and
calls the function. From the tracking issue (#3832):

```rust
fn foo(x: u8, y: u8) { ... }

#[kani::proof]
fn foo_proof() {
  let x = kani::any();
  let y = kani::any();
  foo(x, y);
}
```

**Thesis.** For a large fraction of functions, this harness can be *synthesized
by the compiler* rather than written by hand: detect functions whose arguments
can be represented nondeterministically, generate the harness internally, and
verify it — turning verification from an opt-in, per-function authoring task
into a whole-crate sweep. The research contribution is not only the mechanism
but the *coverage frontier*: which argument/type/function shapes can be
synthesized soundly, and what each extension buys on a real corpus (§6).

Key soundness stance threaded through the whole design: **a bounded or
approximate result must never be presentable as an unbounded/complete one.**
Multiple PRs (#4691, #4721) are explicitly designed so that bounded inputs are
opt-in and loop-unwinding limits surface as *visible* failures rather than
silent bounded passes.

---

## 2. Architecture

Two cooperating layers.

### 2.1 Driver (`kani-driver`)
- `kani-driver/src/args/autoharness_args.rs` — subcommand + CLI surface
  (`CommonAutoharnessArgs`, `Cargo`/`Standalone` variants).
- `kani-driver/src/autoharness/mod.rs` — orchestration; consumes metadata,
  reports selected vs skipped functions (with reasons), invokes the runner.
- Reuses the standard verification pipeline (`harness_runner`, metadata,
  `call_single_file`, `session`).

### 2.2 Compiler (`kani-compiler`)
`kani-compiler/src/kani_middle/transform/automatic.rs` — two MIR transform passes:

1. **`AutomaticHarnessPass`** — transforms the dummy body of an
   `automatic_harness` Kani intrinsic into an actual proof harness for a target
   function: for each argument, emit a `kani::any()` (via `call_kani_any_for_ty`)
   and then call the function.
2. **`AutomaticArbitraryPass`** — synthesizes `T::any()` implementations for
   structs/enums that do **not** implement `Arbitrary` in source but can derive
   it (fields recursively nondeterministic). This is what lets autoharness cover
   plain user structs without any Kani annotations.

Both share `call_kani_any_for_ty`, so improvements (references, invariants,
pointers, …) apply uniformly to top-level arguments and to nested ADT fields.

Supporting compiler files: `codegen_units.rs` (per-unit `determine_targets`
filtering + automatic-harness metadata generation), `kani_functions.rs`
(`KaniModel` registry — e.g. `AssumeSafe`), `metadata.rs`, `compiler_interface.rs`.

### 2.3 Metadata contract (`kani_metadata`)
- `AutomaticHarnessKind`, per-harness metadata, and the **skip taxonomy**
  `AutoHarnessSkipReason` (`kani_metadata/src/lib.rs`) — this enum *is* the
  coverage-frontier vocabulary and is worth citing directly in the paper:
  - `GenericFn` — function is generic (see #4679/#4706/#4726).
  - `KaniImpl` — Kani-internal (existing harness, Kani assoc. item, contract
    instrumentation).
  - `MissingArbitraryImpl(Vec<(name, type)>)` — ≥1 argument neither implements
    nor can derive `Arbitrary`. **The per-type histogram of this reason is the
    primary driver of the extension roadmap** (§6).
  - `NoBody` — no MIR body (e.g. extern).
  - `UserFilter` — excluded by `--include/--exclude-pattern`.

### 2.4 Library (`kani_core` / `kani`)
- `library/kani_core/src/invariant.rs` — `generate_invariant!` macro defining
  the `Invariant` trait, its trivial primitive impls, and the `assume_safe`
  model (post-#4677; also available in `no_core`).
- Generation models live alongside other Kani models (`kani_core`), e.g.
  `AssumeSafe` and the in-flight `AnyPtr`/`any_box`/`any_rc`/`any_arc`/`nondet_fn*`.

---

## 3. Design decisions (with rationale, for the paper)

- **`--harness` is driver-only; `--include/--exclude-function` go to the
  compiler.** From origin PR #3874: autoharness crates have *far* more eligible
  functions than hand-written harnesses, so pushing selection into the compiler
  avoids codegen of thousands of unwanted harnesses. Manual `--harness` filters
  post-codegen because manual harness counts are small.
- **Harnesses are internal.** No source changes; the user only sees results.
  (An opt-in "write harnesses back to file" flag was floated — #3832 comment,
  2025-03-25 — not built.)
- **`-Z autoharness` implies `-Z function-contracts` and `-Z loop-contracts`.**
  If a target has a contract, generate `#[kani::proof_for_contract]` instead of
  `#[kani::proof]`; loop contracts are respected too.
- **Assertions vs assumptions of invariants.** Autoharness *assumes* input
  safety invariants (see #4677) but does not *assert* them on outputs; that
  stays the job of `#[kani::ensures(|r| r.is_safe())]`.
- **Automatic `Arbitrary` derivation is autoharness-only** — regular Kani does
  not synthesize `Arbitrary`.

---

## 4. Capabilities and limitations

### Supported on `main` today
- Functions whose args all implement `Arbitrary` (Kani- or user-provided).
- Structs/enums that can *derive* `Arbitrary` (compiler-synthesized), incl.
  nested.
- Contract harnesses (function + loop contracts).
- References `&T` / `&mut T` where the pointee qualifies (#4234).
- Default timeout + loop-unwinding bounds; include/exclude **regex** filters;
  `--list`; skip logging with reasons.
- Type **safety-invariant assumption** for generated ADT values, incl. nested
  (#4677 — merged into the series head; assumes `v.is_safe()`).

### Known limitations on `main` (from docs + roadmap)
- **Generic functions**: not generated (a monomorphic instantiation reachable
  via an eligible caller may still be verified transitively). Addressed by the
  open series (#4679, #4706, #4726).
- **Non-ADT invariants** (tuples/arrays): not assumed.
- **Closures**: historically unsupported — (1) can't distinguish
  Kani-instrumentation closures (#3921, since closed), (2) `Instance` resolution
  from a closure `CrateItem` failed. `Fn`-bounded params tackled by #4726.
- **Raw pointers**: skipped as "Missing Arbitrary" (addressed by #4678).
- Compiler pulls in a couple of Kani models when run on std (`to_isize`,
  `MemoryInitializationState::new`) — #3832 comment 2025-05-15.
- Tuple-struct constructor functions were spuriously treated as verifiable
  functions (MIR inserts a constructor fn) — #4189, fixed.

---

## 5. In-flight PR series (tautschnig, opened Jul 28 – Aug 7 2026)

Worked in issue order. All target `main`; all under milestone #33. States as of
2026-08-19 (`dirty` = needs rebase; `blocked` = clean, awaiting review; several
are stacked — review only the last commit).

| Order | PR | Contribution | Size | State |
|---|----|--------------|------|-------|
| 1 | [#4677](https://github.com/model-checking/kani/pull/4677) | Assume safety invariants of generated ADT values (nested) via `AssumeSafe` model | +439/−141 | **approved, mergeable** (rebased 2026-08-18) |
| 2 | [#4678](https://github.com/model-checking/kani/pull/4678) | Raw pointer args (`*const/*mut T`, nested) via `AnyPtr`: null / OOB / valid allocation states | +328/−41 | dirty |
| 3 | [#4679](https://github.com/model-checking/kani/pull/4679) | Generic fns: one monomorphic instantiation; type params from `{i32,u32,usize,bool,char}` chosen via trait solver (`ObligationCtxt`) | +345/−93 | blocked |
| 4 | [#4691](https://github.com/model-checking/kani/pull/4691) | `&[T]`/`&mut [T]`/`&str` args, **bounded**, opt-in `--bounded-arguments` (~1,400 skips in top-100) | +541/−69 | dirty |
| 5 | [#4693](https://github.com/model-checking/kani/pull/4693) | `BoundedArbitrary` arg types (`bounded_any::<T,4>`); stacked on #4691 | +785/−83 | dirty |
| 6 | [#4694](https://github.com/model-checking/kani/pull/4694) | Do **not** synthesize `Arbitrary` for structs with reference fields (dangling-ref false alarm) | +57/−6 | dirty |
| 7 | [#4698](https://github.com/model-checking/kani/pull/4698) | Smart pointers `Box`/`Rc`/`Arc` of *derivable* pointees (`any_box/any_rc/any_arc`); stacked on #4697 | +411/−27 | dirty |
| 8 | [#4701](https://github.com/model-checking/kani/pull/4701) | `Debug`/`Display` impls: format a nondet value into a real `Formatter` (~1,900 skips — largest "Missing Arbitrary" type) | +226/−4 | dirty |
| 9 | [#4705](https://github.com/model-checking/kani/pull/4705) | Verify harnesses in **parallel by default** (`-j`); num-traits 1800s→330s for 1,983 harnesses | +107/−25 | dirty |
| 10 | [#4706](https://github.com/model-checking/kani/pull/4706) | Per-parameter + trait-impl-derived generic instantiation; wider primitives incl. floats (~8,700 "Generic Function" skips) | +530/−93 | blocked |
| 11 | [#4716](https://github.com/model-checking/kani/pull/4716) | Assume layout niches (`rustc_layout_scalar_valid_range`, e.g. `NonZero`) of generated scalars — soundness fix | +231/−18 | dirty |
| 12 | [#4717](https://github.com/model-checking/kani/pull/4717) | Constructor-based generation `--constructor-args` for private-field structs (194+ false-alarm harnesses in top-100) | +907/−27 | dirty |
| 13 | [#4718](https://github.com/model-checking/kani/pull/4718) | Mine constructor assertions into value **filters** (assert-guarded representation constructors) | +1435/−27 | dirty |
| 14 | [#4721](https://github.com/model-checking/kani/pull/4721) | **Unbounded** `&[T]`/`&mut [T]`/`Vec<T>` of primitives; unwinding failures stay visible | +1844/−29 | dirty |
| 15 | [#4722](https://github.com/model-checking/kani/pull/4722) | Mine type invariants from a type's *own* assertions (asserted on ≥2 methods; post-dominance admission) — 1,977 sites across 131/500 crates | +3029/−32 | dirty |
| 16 | [#4726](https://github.com/model-checking/kani/pull/4726) | Instantiate `Fn`/`FnMut`/`FnOnce`-bounded params with nondet closures (fn-item models); stacked on #4706 | +1056/−116 | **draft** |

**Stacking graph:** #4693→#4691; #4698→#4697; #4706→#4679; #4726→#4706;
#4717/#4718/#4721/#4722 chain on #4716 (→#4717→#4718→#4721→#4722).

---

## 6. Evaluation data (crates.io corpus)

Hard numbers surfaced in the PR series and #3832 — the empirical backbone of the
paper. All from a **top-100 / top-500 crates.io** evaluation driven off the
tracking issue.

| Metric | Value | Source |
|---|---|---|
| `Formatter` args (largest single "Missing Arbitrary" type) | ~1,900 skipped fns | #4701 |
| Slice/string args (`&[T]`/`&mut [T]`/`&str`) | ~1,400 skipped fns | #4691 |
| Generic fns w/ no satisfying primitive candidate | ~8,700 skipped fns | #4706 |
| Private-invariant false alarms (nondet receiver) | 194+ harnesses (top-100 triage) | #4717 |
| Own-assertion invariant sites | 1,977 sites across 131 of top-500 crates | #4722 |
| `Fn`- vs `Iterator`-bounded signatures | 2,373 vs 612 (top-500) | #4726 |
| Parallelism win (num-traits) | 1800s timeout → 330s for 1,983 harnesses (`-j16`) | #4705 |
| Crates hitting 30-min cap (sequential) | 12 of top-100 | #4705 |

> TODO: get the *baseline* eligible-function counts (how many functions
> autoharness covers before this series) and the post-series delta, to frame
> these as coverage gains rather than raw skip counts.

---

## 7. Historical context / prehistory (pre-tracking-issue)

The milestone also archives 2022–2024 harness-UX work that motivates
autoharness (multi-harness runs, `--list-harnesses`, per-harness codegen, empty-
harness handling, naming collisions). Notable ancestors:
- Per-harness code generation (#1855, 2023) — prerequisite for whole-crate sweeps.
- `--list-harnesses` API (#1612) — becomes autoharness `--list`.
- Multiple `--harness` arguments (#1778, #2118) — filtering model.
- Contract-harness macro (#3590) — relationship to `proof_for_contract`.

Full chronological list: milestone #33 (61 items: 26 open / 35 closed at last sync).

---

## 8. Changelog

Merged PRs land here as we go (most recent first). Nothing from the active
series has merged yet.

- *(pending)* #4677 — assume safety invariants; approved & rebased 2026-08-18.

### Foundational (already on `main`, pre-series)
#3874 subcommand · #3922 misc · #3942 `_`-arg + suffix · #3948 metadata + std ·
#3952 `--list` · #3971 termination/alpha-order · #4016 contracts-by-default ·
#4017 generation improvements · #4025 filtering · #4043 exit code · #4069 arg
validation · #4144 regex patterns · #4167 derive `Arbitrary` · #4194 derivation
fixes · #4234 references · #4370 SHA-1 unit filenames (fixes #4367 crash).

---

## 9. Open questions to resolve for the paper

- Baseline vs post-series coverage numbers (see §6 TODO).
- Soundness argument for assertion/invariant *mining* (#4718, #4722): the
  admission criteria (post-dominance, ≥2-method frequency filter, call-free
  single-assignment slices) need a precise statement + threat-to-validity.
- How bounded results (#4691/#4693) and unbounded-but-unwinding-limited results
  (#4721) are *reported* to the user, and how the paper frames their soundness.
- Relationship to Kani's contracts story (autoharness as a *contract discovery*
  front-end?).
