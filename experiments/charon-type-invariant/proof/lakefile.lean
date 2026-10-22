import Lake
open Lake DSL

-- The Aeneas Lean library from the release that pins Charon v0.1.286 (nightly-2026.10.14-bbc0151):
-- Aeneas only accepts LLBC from the Charon version it pins.
require aeneas from git "https://github.com/AeneasVerif/aeneas.git" @ "bbc0151747be4e3412ed7b113a0d4b170fba0de8" / "backends" / "lean"

package slotsproof

@[default_target] lean_lib Slots
@[default_target] lean_lib SlotsProof
