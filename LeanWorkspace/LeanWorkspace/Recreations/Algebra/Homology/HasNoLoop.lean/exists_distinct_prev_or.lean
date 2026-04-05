import Mathlib

variable {ι : Type*}

variable (c : ComplexShape ι) [c.HasNoLoop] (j : ι)

theorem exists_distinct_prev_or :
    (∃ (k : ι), c.Rel j k ∧ j ≠ k) ∨ ∀ (k : ι), ¬ c.Rel j k := by
  grind +splitIndPred

