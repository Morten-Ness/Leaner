import Mathlib

open scoped Pointwise

variable {G : Type*} {P : Type*} [AddCommGroup G] [AddTorsor G P]

theorem sub_add_vsub_comm (v₁ v₂ : G) (p₁ p₂ : P) :
    (v₁ - v₂) + (p₁ -ᵥ p₂) = (v₁ +ᵥ p₁) -ᵥ (v₂ +ᵥ p₂) := vadd_vsub_vadd_comm _ _ _ _ |>.symm

