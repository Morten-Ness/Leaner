import Mathlib

open scoped Pointwise

variable {G : Type*} {P : Type*} [AddCommGroup G] [AddTorsor G P]

theorem vadd_vsub_vadd_comm (v₁ v₂ : G) (p₁ p₂ : P) :
    (v₁ +ᵥ p₁) -ᵥ (v₂ +ᵥ p₂) = (v₁ - v₂) + (p₁ -ᵥ p₂) := by
  rw [vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, add_sub_assoc, ← add_comm_sub]

