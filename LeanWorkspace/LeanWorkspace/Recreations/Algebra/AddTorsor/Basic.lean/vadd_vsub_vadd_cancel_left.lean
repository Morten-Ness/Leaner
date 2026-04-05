import Mathlib

open scoped Pointwise

variable {G : Type*} {P : Type*} [AddCommGroup G] [AddTorsor G P]

theorem vadd_vsub_vadd_cancel_left (v : G) (p₁ p₂ : P) : (v +ᵥ p₁) -ᵥ (v +ᵥ p₂) = p₁ -ᵥ p₂ := by
  rw [vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, add_sub_cancel_left]

