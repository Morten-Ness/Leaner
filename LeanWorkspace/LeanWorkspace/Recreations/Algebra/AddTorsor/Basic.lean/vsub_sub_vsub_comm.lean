import Mathlib

open scoped Pointwise

variable {G : Type*} {P : Type*} [AddCommGroup G] [AddTorsor G P]

theorem vsub_sub_vsub_comm (p₁ p₂ p₃ p₄ : P) : p₁ -ᵥ p₂ - (p₃ -ᵥ p₄) = p₁ -ᵥ p₃ - (p₂ -ᵥ p₄) := by
  rw [← vsub_vadd_eq_vsub_sub, vsub_vadd_comm, vsub_vadd_eq_vsub_sub]

