import Mathlib

open scoped Pointwise

variable {G : Type*} {P : Type*} [AddCommGroup G] [AddTorsor G P]

theorem vsub_vadd_comm (p₁ p₂ p₃ : P) : (p₁ -ᵥ p₂ : G) +ᵥ p₃ = (p₃ -ᵥ p₂) +ᵥ p₁ := by
  rw [← @vsub_eq_zero_iff_eq G, vadd_vsub_assoc, vsub_vadd_eq_vsub_sub]
  simp

