import Mathlib

variable {F α β γ : Type*}

variable [InvolutiveInv α] {s t : Set α} {a : α}

theorem image_inv_of_apply_inv_eq {f g : α → β} (H : ∀ x ∈ s, f x⁻¹ = g x) :
    f '' (s⁻¹) = g '' s := by
  rw [← Set.image_inv_eq_inv, Set.image_image]; exact Set.image_congr H

