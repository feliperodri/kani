# Tests that need CBMC's loop-assigns inference not to inline the aliasing model

CBMC's contract instrumentation (DFCC) infers a loop's write set by inlining every call in the
harness, including the aliasing checks' model, which costs more memory than CI has, and by an
alias analysis that the model's calls make imprecise. These tests pass with a CBMC whose inference
leaves functions it does not instrument (`__CPROVER_*`, `__VERIFIER_*`) out (local patch to
`dfcc_infer_loop_assigns.cpp`, to be proposed upstream). The `fixme` in the directory name makes
compiletest skip them.
