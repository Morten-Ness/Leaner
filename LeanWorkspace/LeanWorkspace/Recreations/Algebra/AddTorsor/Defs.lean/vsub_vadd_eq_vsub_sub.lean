import Mathlib

variable {G : Type*} {P : Type*} [AddGroup G] [T : AddTorsor G P]

theorem vsub_vadd_eq_vsub_sub (p₁ p₂ : P) (g : G) : p₁ -ᵥ (g +ᵥ p₂) = p₁ -ᵥ p₂ - g := by
  rw [← add_right_inj (p₂ -ᵥ p₁ : G), vsub_add_vsub_cancel, ← neg_vsub_eq_vsub_rev, vadd_vsub, ←
    add_sub_assoc, ← neg_vsub_eq_vsub_rev, neg_add_cancel, zero_sub]

