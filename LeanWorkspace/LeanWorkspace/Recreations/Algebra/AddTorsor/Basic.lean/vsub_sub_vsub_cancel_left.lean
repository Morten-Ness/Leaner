import Mathlib

open scoped Pointwise

variable {G : Type*} {P : Type*} [AddCommGroup G] [AddTorsor G P]

theorem vsub_sub_vsub_cancel_left (p₁ p₂ p₃ : P) : p₃ -ᵥ p₂ - (p₃ -ᵥ p₁) = p₁ -ᵥ p₂ := by
  rw [sub_eq_add_neg, neg_vsub_eq_vsub_rev, add_comm, vsub_add_vsub_cancel]

