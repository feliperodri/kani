# Issue: Other Fixme Tests (Miscellaneous / Pre-existing)

## Summary

These fixme tests were either pre-existing before the nightly-2026-04-13 upgrade
or have issues unrelated to the main categories (bodyless items, vtable mismatch,
SIMD, uninit transforms).

## Affected Fixme Tests

### Function contracts (ZST modifies)
- `tests/expected/function-contract/modifies/fixme_zst_pass.rs`

### Float-to-int (f16/f128 not fully supported)
- `tests/kani/Intrinsics/FloatToInt/fixme_float_to_int_f16_f128.rs`

### UI warning test
- `tests/ui/logging/warning/fixme_trivial.rs`

### Script-based tests (various infrastructure issues)
- `tests/script-based-pre/fixme_playback_already_existing/`
- `tests/script-based-pre/fixme_playback_multi_harness_multi_inject/`
- `tests/script-based-pre/fixme_playback_no_rustfmt/`
- `tests/script-based-pre/fixme_playback_opts/`
- `tests/script-based-pre/fixme_std_codegen/`
- `tests/script-based-pre/fixme_tool-scanner/`

### Cargo-kani vecdeque-cve (expected output changes)
- `tests/cargo-kani/vecdeque-cve/fixme_abstract_remove_maintains_invariant.expected`
- `tests/cargo-kani/vecdeque-cve/fixme_abstract_reserve_maintains_invariant_with_cve.expected`
- `tests/cargo-kani/vecdeque-cve/fixme_abstract_reserve_maintains_invariant_with_cve_fixed.expected`
- `tests/cargo-kani/vecdeque-cve/fixme_minimal_example_with_cve_fixed.expected`
- `tests/cargo-kani/vecdeque-cve/fixme_minimal_example_with_cve_should_fail.expected`
- `tests/cargo-kani/vecdeque-cve/fixme_reserve_available_capacity_is_no_op.expected`
- `tests/cargo-kani/vecdeque-cve/fixme_reserve_available_capacity_should_fail.expected`
- `tests/cargo-kani/vecdeque-cve/fixme_reserve_more_capacity_still_works.expected`
- `tests/cargo-kani/vecdeque-cve/fixme_reserve_more_capacity_works.expected`

## Notes

Many of these pre-date the current toolchain upgrade and track separate known
limitations. They should be investigated individually.
