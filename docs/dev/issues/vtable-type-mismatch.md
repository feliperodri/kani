# Issue: Vtable Type Mismatch (Fat Pointer Metadata Cast)

## Summary

When codegen encounters `std::ptr::metadata` on a trait object (e.g., `dyn Animal`),
it panics with a type mismatch error during a vtable pointer cast in
`cprover_bindings/src/goto_program/expr.rs:697`:

```
thread 'rustc' panicked at cprover_bindings/src/goto_program/expr.rs:697:13:
Can't cast
Expr { ... typ: Pointer { typ: StructTag("tag-_206833...::vtable") } ... }
StructTag("tag-_317151225504234823118556439907602344177")
```

The expression has one vtable struct tag but is being cast to a different vtable
struct tag. Both represent the same logical vtable type but have different numeric
identifiers.

## Impact

This causes **55 test failures** in the kani regression suite after the
nightly-2026-04-29 toolchain upgrade. It affects ALL code that uses trait objects
(dyn Trait), including:
- Fat pointers (Box<dyn T>, &dyn T, *const dyn T)
- Unsized coercions
- Dynamic dispatch
- println!/format! (uses dyn Error internally)

## Root Cause

The new toolchain introduces `std::ptr::metadata` as a reachable monomorphized item
for trait objects. When Kani codegens this function, it extracts the vtable pointer
from a fat pointer and attempts to cast it. The source vtable type (from the FatPtr
struct) and the target vtable type (expected by the cast) have different struct tags
despite being structurally equivalent.

This likely stems from the vtable type being generated at two different points during
codegen, each producing a different tag.

## Affected Tests (55 failures in kani suite)

### DynTrait tests
- `tests/kani/DynTrait/main.rs`
- `tests/kani/DynTrait/boxed_trait.rs`
- `tests/kani/DynTrait/boxed_debug_cast.rs`
- `tests/kani/DynTrait/dyn_fn_param_closure.rs`
- `tests/kani/DynTrait/dyn_fn_param_closure_capture.rs`
- `tests/kani/DynTrait/nested_boxes.rs`
- `tests/kani/DynTrait/object_safe_trait.rs`
- `tests/kani/DynTrait/unsized_cast.rs`
- `tests/kani/DynTrait/unsized_rc_cast.rs`
- `tests/kani/DynTrait/vtable_duplicate_field_override.rs`
- `tests/kani/DynTrait/vtable_duplicate_fields.rs`
- `tests/kani/DynTrait/vtable_restrictions.rs`
- `tests/kani/DynTrait/vtable_size_align_drop.rs`

### FatPointers tests
- `tests/kani/FatPointers/boxtrait.rs`
- `tests/kani/FatPointers/boxmuttrait.rs`
- `tests/kani/FatPointers/boxslice1.rs`
- `tests/kani/FatPointers/boxslice2.rs`
- `tests/kani/FatPointers/metadata.rs`

### UnsizedCoercion tests
- `tests/kani/UnsizedCoercion/box_coercion.rs`
- `tests/kani/UnsizedCoercion/box_inner_coercion.rs`
- `tests/kani/UnsizedCoercion/box_outer_coercion.rs`
- `tests/kani/UnsizedCoercion/double_coercion.rs`
- `tests/kani/UnsizedCoercion/rc_outer_coercion.rs`

### Projection tests
- `tests/kani/Projection/dyn_dyn_projection.rs`
- `tests/kani/Projection/dyn_slice_projection.rs`
- `tests/kani/Projection/slice_dyn_projection.rs`

### Drop tests (use dyn trait)
- `tests/kani/Drop/drop_boxed_dyn.rs`
- `tests/kani/Drop/drop_nested_boxed_dyn.rs`
- `tests/kani/Drop/drop_slice.rs`
- `tests/kani/Drop/dyn_struct_member.rs`
- `tests/kani/Drop/rc_dyn.rs`

### Other tests using trait objects
- `tests/kani/AggregateRvalue/dyn_ptr.rs`
- `tests/kani/AsyncAwait/spawn.rs`
- `tests/kani/Cast/from_be_bytes.rs`
- `tests/kani/Closure/main.rs`
- `tests/kani/Coroutines/issue-2434.rs`
- `tests/kani/Coroutines/rustc-coroutine-tests/smoke-resume-args.rs`
- `tests/kani/FunctionContracts/modify_slice_elem.rs`
- `tests/kani/Intrinsics/AlignOfVal/align_of_fat_ptr.rs`
- `tests/kani/Intrinsics/Copy/copy_nonoverlapping_append.rs`
- `tests/kani/Intrinsics/Forget/forget_ok.rs`
- `tests/kani/Intrinsics/SizeOfVal/size_of_fat_ptr.rs`
- `tests/kani/Intrinsics/Volatile/load.rs`
- `tests/kani/Iterator/into_iter.rs`
- `tests/kani/NondetVectors/bytes.rs`
- `tests/kani/PointerOffset/offset_from_vec.rs`
- `tests/kani/SizeAndAlignOfDst/main.rs`
- `tests/kani/SizeAndAlignOfDst/unsized_tail.rs`
- `tests/kani/Strings/parse.rs`
- `tests/kani/Stubbing/std_fs_read.rs`
- `tests/kani/Stubbing/use_std_fs_read.rs`
- `tests/kani/Vectors/any/push_slow.rs`
- `tests/kani/Vectors/any/resize.rs`
- `tests/kani/Vectors/any/sorting.rs`
- `tests/kani/Vectors/vector_extend_loop.rs`

### Fixme tests (also affected, already marked)
- `tests/kani/Print/fixme_main.rs` (and all Print fixme tests)
- `tests/expected/dangling-ptr-println/fixme_main.rs`
- `tests/expected/panic/panic-2021/fixme_messages.rs`

## Potential Fix

The vtable struct tag generation needs to be made consistent. When `codegen_ty`
creates a vtable type for a trait object, it should reuse the same tag regardless
of whether the type is encountered via:
1. The FatPtr struct definition
2. A cast target in `ptr::metadata`

Investigate `codegen_vtable_type` and the fat pointer construction in `typ.rs`
to ensure a single canonical tag is used per trait.
