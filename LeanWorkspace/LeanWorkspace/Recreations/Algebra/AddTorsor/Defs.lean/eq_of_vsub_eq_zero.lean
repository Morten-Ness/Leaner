import Mathlib

variable {G : Type*} {P : Type*} [AddGroup G] [T : AddTorsor G P]

theorem eq_of_vsub_eq_zero {p₁ p₂ : P} (h : p₁ -ᵥ p₂ = (0 : G)) : p₁ = p₂ := by
  rw [← vsub_vadd p₁ p₂, h, zero_vadd]

