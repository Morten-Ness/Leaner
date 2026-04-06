import Mathlib

variable {F α β γ : Type*}

variable [InvolutiveInv α] {s t : Set α} {a : α}

theorem inv_eq_self_iff_inv_subset : s⁻¹ = s ↔ s⁻¹ ⊆ s := by
  constructor
  · intro h
    simpa [h]
  · intro h
    apply le_antisymm h
    intro x hx
    have : x⁻¹ ∈ s⁻¹ := by
      simpa using hx
    exact h this
