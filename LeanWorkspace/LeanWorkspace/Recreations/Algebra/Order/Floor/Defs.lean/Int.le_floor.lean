import Mathlib

variable {F α β : Type*}

variable [Ring α] [LinearOrder α] [FloorRing α] {z : ℤ} {a b : α}

private noncomputable def floorAux {α} [Ring α] [PartialOrder α] [IsStrictOrderedRing α] {x : α}
    (below : ∃ n : ℤ, n ≤ x) (above : ∃ n : ℤ, x ≤ n) :
    {n : ℤ // n ≤ x ∧ ∀ m : ℤ, m ≤ x → m ≤ n} := by
  let n := Classical.indefiniteDescription _ above
  refine Int.greatestOfBdd (P := (· ≤ x)) n.1 (fun m hm ↦ ?_) below
  rw [← Int.cast_le (R := α)]
  exact hm.trans n.2


theorem le_floor : z ≤ ⌊a⌋ ↔ (z : α) ≤ a := (Int.gc_coe_floor z a).symm

