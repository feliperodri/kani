# Issue: SIMD Unsupported Intrinsics

## Summary

Several SIMD intrinsics (`simd_splat`, `simd_bitmask`, comparison operators on SIMD
types) are not implemented in Kani's codegen, causing verification failures:

```
simd_splat is not currently supported by Kani
```

## Root Cause

Kani's SIMD intrinsic handling in `codegen/intrinsic.rs` does not cover all SIMD
operations. The new toolchain may also generate different SIMD lowerings that expose
previously-untriggered code paths.

## Affected Fixme Tests

### Portable SIMD
- `tests/kani/SIMD/fixme_portable_simd.rs`
- `tests/kani/SIMD/fixme_simd_float_portable.rs`

### SIMD comparison operators (new tests split from existing)
- `tests/kani/SIMD/fixme_array_simd_repr_ge.rs`
- `tests/kani/SIMD/fixme_multi_field_simd_ge.rs`

### SIMD bitmask
- `tests/kani/SIMD/fixme_simd_bitmask_equiv.rs`
- `tests/kani/Intrinsics/SIMD/Operators/fixme_bitmask.rs`

## Potential Fix

Implement the missing SIMD intrinsics in `codegen/intrinsic.rs`. The `simd_splat`
intrinsic creates a vector with all lanes set to the same value — this should be
straightforward to implement as a repeated-element array construction.
