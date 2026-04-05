import Mathlib

variable {F α β γ : Type*}

variable [InvolutiveInv α] {s t : Set α} {a : α}

theorem inv_eq_empty : s⁻¹ = ∅ ↔ s = ∅ := by
  rw [← Set.image_inv_eq_inv, image_eq_empty]

