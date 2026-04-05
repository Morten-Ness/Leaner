import Mathlib

variable {R S M M₂ : Type*}

variable [Ring R] [AddCommGroup M] [Module R M] (r : R) (x : M)

theorem neg_smul_neg : -r • -x = r • x := by rw [neg_smul, smul_neg, neg_neg]

