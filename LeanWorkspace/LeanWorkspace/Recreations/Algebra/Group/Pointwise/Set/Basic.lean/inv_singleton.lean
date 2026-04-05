import Mathlib

variable {F α β γ : Type*}

variable [InvolutiveInv α] {s t : Set α} {a : α}

theorem inv_singleton (a : α) : ({a} : Set α)⁻¹ = {a⁻¹} := by
  rw [← Set.image_inv_eq_inv, image_singleton]

