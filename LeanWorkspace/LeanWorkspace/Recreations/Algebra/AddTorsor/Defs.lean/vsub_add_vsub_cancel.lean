import Mathlib

variable {G : Type*} {P : Type*} [AddGroup G] [T : AddTorsor G P]

theorem vsub_add_vsub_cancel (p₁ p₂ p₃ : P) : p₁ -ᵥ p₂ + (p₂ -ᵥ p₃) = p₁ -ᵥ p₃ := by
  apply vadd_right_cancel p₃
  rw [add_vadd, vsub_vadd, vsub_vadd, vsub_vadd]

