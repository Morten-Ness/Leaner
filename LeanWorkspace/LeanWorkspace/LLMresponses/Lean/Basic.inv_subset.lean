import Mathlib

variable {F α β γ : Type*}

variable [InvolutiveInv α] {s t : Set α} {a : α}

theorem inv_subset : s⁻¹ ⊆ t ↔ s ⊆ t⁻¹ := by
  constructor
  · intro h x hx
    have hx' : x⁻¹ ∈ s⁻¹ := by simpa using hx
    exact h hx'
  · intro h x hx
    have hx' : x⁻¹ ∈ s := by simpa using hx
    have ht : x⁻¹ ∈ t⁻¹ := h hx'
    simpa using ht
