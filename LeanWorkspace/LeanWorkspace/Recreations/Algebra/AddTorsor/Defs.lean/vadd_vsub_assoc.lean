import Mathlib

variable {G : Type*} {P : Type*} [AddGroup G] [T : AddTorsor G P]

theorem vadd_vsub_assoc (g : G) (p₁ p₂ : P) : (g +ᵥ p₁) -ᵥ p₂ = g + (p₁ -ᵥ p₂) := by
  apply vadd_right_cancel p₂
  rw [vsub_vadd, add_vadd, vsub_vadd]

