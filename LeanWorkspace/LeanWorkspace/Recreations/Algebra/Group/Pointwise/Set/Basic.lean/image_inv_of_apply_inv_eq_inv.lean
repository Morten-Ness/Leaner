import Mathlib

variable {F α β γ : Type*}

variable [InvolutiveInv α] {s t : Set α} {a : α}

theorem image_inv_of_apply_inv_eq_inv [InvolutiveInv β] {f g : α → β}
    (H : ∀ x ∈ s, f x⁻¹ = (g x)⁻¹) : f '' s⁻¹ = (g '' s)⁻¹ := by
  conv_rhs => rw [← Set.image_inv_eq_inv, image_image, ← Set.image_inv_of_apply_inv_eq H]

