import Mathlib

variable {R S M M₂ : Type*}

variable [Ring R] [AddCommGroup M] [Module R M] (r : R) (x : M)

theorem sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y := by
  simp [add_smul, sub_eq_add_neg]

