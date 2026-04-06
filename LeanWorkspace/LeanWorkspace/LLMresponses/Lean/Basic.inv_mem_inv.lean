import Mathlib

variable {F α β γ : Type*}

variable [InvolutiveInv α] {s t : Set α} {a : α}

theorem inv_mem_inv : a⁻¹ ∈ s⁻¹ ↔ a ∈ s := by
  rw [Set.mem_inv, inv_inv]
