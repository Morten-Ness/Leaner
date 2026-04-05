import Mathlib

variable {F α β : Type*}

private noncomputable def floorAux {α} [Ring α] [PartialOrder α] [IsStrictOrderedRing α] {x : α}
    (below : ∃ n : ℤ, n ≤ x) (above : ∃ n : ℤ, x ≤ n) :
    {n : ℤ // n ≤ x ∧ ∀ m : ℤ, m ≤ x → m ≤ n} := by
  let n := Classical.indefiniteDescription _ above
  refine Int.greatestOfBdd (P := (· ≤ x)) n.1 (fun m hm ↦ ?_) below
  rw [← Int.cast_le (R := α)]
  exact hm.trans n.2


theorem exists_floor' {α} [Ring α] [PartialOrder α] [IsStrictOrderedRing α] (x : α)
    (below : ∃ n : ℤ, n ≤ x) (above : ∃ n : ℤ, x ≤ n) :
    ∃ fl : ℤ, ∀ z : ℤ, z ≤ fl ↔ (z : α) ≤ x := by
  refine ⟨_, fun n ↦ ⟨?_, (floorAux below above).2.2 _⟩⟩
  rw [← Int.cast_le (R := α)]
  exact le_trans' (floorAux below above).2.1

