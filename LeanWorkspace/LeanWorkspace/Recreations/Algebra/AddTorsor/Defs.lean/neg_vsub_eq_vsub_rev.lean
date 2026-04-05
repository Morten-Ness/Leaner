import Mathlib

variable {G : Type*} {P : Type*} [AddGroup G] [T : AddTorsor G P]

theorem neg_vsub_eq_vsub_rev (p₁ p₂ : P) : -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁ := by
  refine neg_eq_of_add_eq_zero_right (vadd_right_cancel p₁ ?_)
  rw [vsub_add_vsub_cancel, vsub_self]

