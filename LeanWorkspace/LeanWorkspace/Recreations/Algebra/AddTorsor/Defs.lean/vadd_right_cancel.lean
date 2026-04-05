import Mathlib

variable {G : Type*} {P : Type*} [AddGroup G] [T : AddTorsor G P]

theorem vadd_right_cancel {g₁ g₂ : G} (p : P) (h : g₁ +ᵥ p = g₂ +ᵥ p) : g₁ = g₂ := by
  rw [← vadd_vsub g₁ p, h, vadd_vsub]

