import Mathlib

open scoped Pointwise

variable {G : Type*} {P : Type*} [AddCommGroup G] [AddTorsor G P]

theorem vadd_eq_vadd_iff_sub_eq_vsub {v₁ v₂ : G} {p₁ p₂ : P} :
    v₁ +ᵥ p₁ = v₂ +ᵥ p₂ ↔ v₂ - v₁ = p₁ -ᵥ p₂ := by
  rw [vadd_eq_vadd_iff_neg_add_eq_vsub, neg_add_eq_sub]

