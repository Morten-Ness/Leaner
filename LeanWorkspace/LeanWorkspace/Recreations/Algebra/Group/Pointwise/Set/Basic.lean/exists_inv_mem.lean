import Mathlib

variable {F α β γ : Type*}

variable [InvolutiveInv α] {s t : Set α} {a : α}

theorem exists_inv_mem {p : α → Prop} : (∃ x, x⁻¹ ∈ s ∧ p x) ↔ ∃ x ∈ s, p x⁻¹ := by
  rw [← (Equiv.inv _).exists_congr_right]
  simp

