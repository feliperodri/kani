# Tests that need CBMC with diffblue/cbmc#9238

These tests pass with a CBMC that includes
[diffblue/cbmc#9238](https://github.com/diffblue/cbmc/pull/9238), which folds casts of pointer
constants to integers. Without it, the tags that the aliasing checks read from shadow memory stay
symbolic, and these tests take minutes and several GB each (up to 8 GB with CBMC 6.11.0), which
is more than CI runners have. The `fixme` in the directory name makes compiletest skip them.

Move them back to `tests/expected/aliasing` once Kani's CBMC version includes that change.
