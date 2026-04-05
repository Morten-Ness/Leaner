import Mathlib

variable {ι : Type*}

variable (c : ComplexShape ι) [c.HasNoLoop] (j : ι)

theorem exists_distinct_next_or :
    (∃ (i : ι), c.Rel i j ∧ i ≠ j) ∨ ∀ (i : ι), ¬ c.Rel i j := by
  grind +splitIndPred

