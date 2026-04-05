import Mathlib

variable {F α β γ : Type*}

variable [InvolutiveInv α] {s t : Set α} {a : α}

theorem inv_subset : s⁻¹ ⊆ t ↔ s ⊆ t⁻¹ := by rw [← Set.inv_subset_inv, inv_inv]

