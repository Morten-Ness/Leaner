import Mathlib

variable {K : Type*} [Field K] [NeZero (2 : K)] {a b c : K}

theorem discrim_eq_zero_iff (ha : a ≠ 0) :
    discrim a b c = 0 ↔ (∃! x, a * (x * x) + b * x + c = 0) := by
  refine ⟨fun hd => ?_, discrim_eq_zero_of_existsUnique ha⟩
  simp_rw [quadratic_eq_zero_iff_of_discrim_eq_zero ha hd, existsUnique_eq]

