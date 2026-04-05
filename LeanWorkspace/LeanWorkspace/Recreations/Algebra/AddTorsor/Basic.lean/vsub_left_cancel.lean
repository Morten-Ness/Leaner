import Mathlib

open scoped Pointwise

variable {G : Type*} {P : Type*} [AddGroup G] [T : AddTorsor G P]

theorem vsub_left_cancel {p₁ p₂ p : P} (h : p₁ -ᵥ p = p₂ -ᵥ p) : p₁ = p₂ := by
  rwa [← sub_eq_zero, vsub_sub_vsub_cancel_right, vsub_eq_zero_iff_eq] at h

