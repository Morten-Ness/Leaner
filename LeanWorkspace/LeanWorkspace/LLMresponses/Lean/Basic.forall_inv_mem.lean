import Mathlib

variable {F α β γ : Type*}

variable [InvolutiveInv α] {s t : Set α} {a : α}

theorem forall_inv_mem {p : α → Prop} : (∀ x, x⁻¹ ∈ s → p x) ↔ ∀ x ∈ s, p x⁻¹ := by
  constructor
  · intro h x hx
    exact h x⁻¹ (by simpa using hx)
  · intro h x hx
    simpa using h x⁻¹ hx
