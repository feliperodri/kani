import Lake
open Lake DSL

require aeneas from "/local/home/felisous/untrusted/aeneas-1014/backends/lean"

package slotsproof

@[default_target] lean_lib Slots
@[default_target] lean_lib SlotsProof
