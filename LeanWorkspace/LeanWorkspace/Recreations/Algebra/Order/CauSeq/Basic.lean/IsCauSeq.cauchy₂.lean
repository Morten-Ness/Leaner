import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Ring β]
  {abv : β → α} [IsAbsoluteValue abv] {f g : ℕ → β}

theorem cauchy₂ (hf : IsCauSeq abv f) {ε : α} (ε0 : 0 < ε) :
    ∃ i, ∀ j ≥ i, ∀ k ≥ i, abv (f j - f k) < ε := by
  refine (hf _ (half_pos ε0)).imp fun i hi j ij k ik => ?_
  rw [← add_halves ε]
  refine lt_of_le_of_lt (abv_sub_le abv _ _ _) (add_lt_add (hi _ ij) ?_)
  rw [abv_sub abv]; exact hi _ ik

