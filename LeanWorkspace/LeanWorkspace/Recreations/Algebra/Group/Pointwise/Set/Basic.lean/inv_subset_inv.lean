import Mathlib

variable {F α β γ : Type*}

variable [InvolutiveInv α] {s t : Set α} {a : α}

theorem inv_subset_inv : s⁻¹ ⊆ t⁻¹ ↔ s ⊆ t := (Equiv.inv α).surjective.preimage_subset_preimage_iff

