/-
Copyright Kani Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT

The type invariant of `Slots<T>` (slots.rs), proved for every `T` on the Lean model that Aeneas
generates from Charon's LLBC (Slots.lean). The model is parametric in `T`, so these theorems cover
every instantiation the Kani harnesses check, and every other one.
-/
import Slots

open Aeneas Aeneas.Std Result

namespace slots

/-- The number of occupied slots. -/
def Slots.count {T : Type} (s : Slots T) : Nat :=
  (if s.a.isSome then 1 else 0) + (if s.b.isSome then 1 else 0)

/-- The type invariant: `len` counts the occupied slots, and `b` is occupied only if `a` is. -/
def Slots.inv {T : Type} (s : Slots T) : Prop :=
  s.len.val = s.count ∧ (s.b.isSome → s.a.isSome)

/-- `new` establishes the invariant. -/
theorem new_spec (T : Type) : new T ⦃ s => s.inv ⦄ := by
  simp [new, Slots.inv, Slots.count]

/-- `push` preserves the invariant, never overflows `len`, and rejects `x` exactly when both
slots are full. -/
theorem push_spec {T : Type} (s : Slots T) (x : T) (h : s.inv) :
    push s x ⦃ r => r.1.inv ∧ (r.2.isSome ↔ s.b.isSome) ⦄ := by
  obtain ⟨hlen, hba⟩ := h
  unfold push
  rcases ha : s.a with _ | va <;> rcases hb : s.b with _ | vb <;>
    simp_all [Slots.inv, Slots.count] <;>
    step as ⟨i, hi⟩ <;> simp_all

/-- `pop` preserves the invariant, never underflows `len`, and returns a value exactly when the
slots are not empty. -/
theorem pop_spec {T : Type} (s : Slots T) (h : s.inv) :
    pop s ⦃ r => r.1.inv ∧ (r.2.isSome ↔ s.a.isSome) ⦄ := by
  obtain ⟨hlen, hba⟩ := h
  unfold pop
  rcases ha : s.a with _ | va <;> rcases hb : s.b with _ | vb <;>
    simp_all [Slots.inv, Slots.count] <;>
    step as ⟨i, hi⟩ <;> simp_all

end slots

#print axioms slots.push_spec
#print axioms slots.pop_spec
#print axioms slots.new_spec
