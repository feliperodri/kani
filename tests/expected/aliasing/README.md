# Aliasing checks litmus tests

Each test was also run under Miri, with `-Zmiri-tree-borrows` and with Stacked Borrows. The file
name says what Miri reports:

- `ok_*`: no undefined behavior under either model.
- `ub_*`: undefined behavior under both models.
- `sb_only_*`: undefined behavior under Stacked Borrows only; Kani follows Tree Borrows and
  verifies them.
- `fixme_*`: undefined behavior that Kani does not check yet; the `.expected` file holds the
  result Kani should give.

Where Kani cannot follow a pointer's provenance, the `.expected` file records the inconclusive
"Kani's aliasing checks do not know which reference this pointer was derived from" failure.
These change as the checks follow more pointers.
