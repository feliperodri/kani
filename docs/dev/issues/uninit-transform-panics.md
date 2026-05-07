# Issue: Uninit/Shadow Transform Panics and dealloc_nonnull

## Summary

The uninitialized memory checking transforms (`-Z uninit-checks`) panic during
compilation when processing certain patterns. Two distinct sub-issues:

1. **`initial_target_visitor.rs` panic**: The delayed UB initial target visitor
   panics when processing shadow memory instrumentation for arrays.

2. **`dealloc_nonnull` codegen failure**: The new stdlib introduces
   `alloc::alloc::dealloc_nonnull(ptr: NonNull<u8>, layout: Layout)` which takes
   `NonNull` directly. Kani's foreign function codegen doesn't handle this new
   function signature.

## Root Cause

1. The uninit transform assumes certain MIR patterns that changed in the new toolchain.
2. `dealloc_nonnull` is a new internal function in the allocator that wraps `__rust_dealloc`
   but takes `NonNull<u8>` instead of `*mut u8`. Kani's allocator model needs updating.

## Affected Fixme Tests

### Shadow memory / uninit array
- `tests/expected/shadow/uninit_array/fixme_test.rs`

### Vec uninit reads (trigger dealloc_nonnull via Vec drop)
- `tests/expected/uninit/vec-read-bad-len/fixme_vec-read-bad-len.rs`
- `tests/expected/uninit/vec-read-semi-init/fixme_vec-read-semi-init.rs`
- `tests/expected/uninit/vec-read-uninit/fixme_vec-read-uninit.rs`
- `tests/kani/Uninit/fixme_atomic.rs`
- `tests/kani/Uninit/fixme_vec-read-init.rs`

### Valid value checks (partially affected)
- `tests/expected/valid-value-checks/fixme_maybe_uninit.rs`
  (1 of 2 harnesses passes; the failing one is expected UB detection)

## Potential Fix

1. Update `initial_target_visitor.rs` to handle the new MIR patterns for array
   initialization.
2. Add `dealloc_nonnull` to Kani's allocator model in `foreign_function.rs`,
   similar to how `__rust_dealloc` is handled but accepting `NonNull<u8>`.
