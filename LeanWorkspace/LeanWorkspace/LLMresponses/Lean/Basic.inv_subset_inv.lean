import Mathlib

variable {F α β γ : Type*}

variable [InvolutiveInv α] {s t : Set α} {a : α}

theorem inv_subset_inv : s⁻¹ ⊆ t⁻¹ ↔ s ⊆ t := by
  constructor
  · intro h x hx
    have hs : x⁻¹ ∈ s⁻¹ := by simpa using hx
    have ht : x⁻¹ ∈ t⁻¹ := h hs
    simpa using ht
  · intro h x hx
    change x⁻¹ ∈ t at *
    exact h hx
