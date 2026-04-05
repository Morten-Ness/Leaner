import Mathlib

open scoped Pointwise

variable {G : Type*} {P : Type*} [AddGroup G] [T : AddTorsor G P]

theorem vsub_right_cancel {p₁ p₂ p : P} (h : p -ᵥ p₁ = p -ᵥ p₂) : p₁ = p₂ := by
  refine vadd_left_cancel (p -ᵥ p₂) ?_
  rw [vsub_vadd, ← h, vsub_vadd]

