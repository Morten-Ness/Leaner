import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable [Ring β] {abv : β → α}

variable [IsAbsoluteValue abv]

theorem abv_pos_of_not_limZero {f : CauSeq β abv} (hf : ¬CauSeq.LimZero f) :
    ∃ K > 0, ∃ i, ∀ j ≥ i, K ≤ abv (f j) := by
  by_contra nk
  refine hf fun ε ε0 => ?_
  simp only [not_exists, not_and, not_forall, not_le] at nk
  obtain ⟨i, hi⟩ := CauSeq.cauchy₃ f (half_pos ε0)
  rcases nk _ (half_pos ε0) i with ⟨j, ij, hj⟩
  refine ⟨j, fun k jk => ?_⟩
  have := lt_of_le_of_lt (abv_add abv _ _) (add_lt_add (hi j ij k jk) hj)
  rwa [sub_add_cancel, add_halves] at this

