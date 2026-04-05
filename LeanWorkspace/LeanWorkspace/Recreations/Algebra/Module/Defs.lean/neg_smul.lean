import Mathlib

variable {R S M M₂ : Type*}

variable [Ring R] [AddCommGroup M] [Module R M] (r : R) (x : M)

theorem neg_smul : -r • x = -(r • x) := eq_neg_of_add_eq_zero_left <| by rw [← add_smul, neg_add_cancel, zero_smul]

