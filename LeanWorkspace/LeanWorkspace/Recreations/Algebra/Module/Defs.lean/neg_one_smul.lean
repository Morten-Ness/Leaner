import Mathlib

variable {R S M M₂ : Type*}

variable [Ring R] [AddCommGroup M] [Module R M] (r : R) (x : M)

theorem neg_one_smul (x : M) : (-1 : R) • x = -x := by simp

