import Mathlib

variable {G : Type*} {P : Type*} [AddGroup G] [T : AddTorsor G P]

theorem vsub_sub_vsub_cancel_right (p₁ p₂ p₃ : P) : p₁ -ᵥ p₃ - (p₂ -ᵥ p₃) = p₁ -ᵥ p₂ := by
  rw [← vsub_vadd_eq_vsub_sub, vsub_vadd]

