# Issue: Bodyless `FnOnce::call_once` (Closure-to-fn-ptr Coercion)

## Summary

When a closure is coerced to a function pointer, the new toolchain (nightly-2026-04-13+)
exposes `FnOnce::call_once` shims as `MonoItem::Fn` without bodies. Kani declares these
functions but cannot codegen them, resulting in verification failures with:

```
Function `<{closure} as FnOnce<(...)>>::call_once` with missing definition is unreachable
```

This also affects iterator adapters and comparison operators that internally use
closure-to-fn-ptr coercion patterns.

## Root Cause

The rustc nightly now emits enum variant constructors and closure shims as monomorphized
items without MIR bodies. Kani's `has_body()` guard prevents codegen panics, but the
resulting bodyless declarations cause CBMC to report them as unreachable.

## Affected Fixme Tests

### Closure tests
- `tests/kani/Closure/fixme_closure_ptr.rs`
- `tests/kani/Closure/fixme_tupled_closure.rs`
- `tests/kani/Closure/fixme_zst_param.rs`

### DynTrait tests (use closures as dyn Fn/FnMut/FnOnce)
- `tests/kani/DynTrait/fixme_boxed_closure.rs`
- `tests/kani/DynTrait/fixme_dyn_fn_mut.rs`
- `tests/kani/DynTrait/fixme_dyn_fn_once.rs`
- `tests/kani/DynTrait/fixme_dyn_fn_param.rs`
- `tests/kani/DynTrait/fixme_nested_closures.rs`

### Drop (closure move semantics)
- `tests/kani/Drop/fixme_drop_after_move_closure_call.rs`

### Iterator (uses closure-based adapters)
- `tests/kani/Iterator/fixme_flat_map.rs`

### Comparison operators (use fn-ptr shims internally)
- `tests/kani/LexicographicCmp/fixme_main.rs`

### Other (trigger FnOnce::call_once via std library internals)
- `tests/kani/ThreadLocalRef/fixme_main.rs`
- `tests/kani/Slice/fixme_pathbuf.rs`

### Coverage test (uses closures)
- `tests/coverage/known_issues/variant/fixme_main.rs`

## Potential Fix

Generate stub bodies for `FnOnce::call_once` shims that forward to the closure's
actual implementation, or handle these items specially in the reachability analysis
to avoid declaring them without bodies.
