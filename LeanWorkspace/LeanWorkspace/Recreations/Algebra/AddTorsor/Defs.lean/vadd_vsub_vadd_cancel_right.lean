import Mathlib

variable {G : Type*} {P : Type*} [AddGroup G] [T : AddTorsor G P]

theorem vadd_vsub_vadd_cancel_right (v₁ v₂ : G) (p : P) : (v₁ +ᵥ p) -ᵥ (v₂ +ᵥ p) = v₁ - v₂ := by
  rw [vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, vsub_self, add_zero]

