import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [InvolutiveInv α] {s : Finset α} {a : α}

theorem mem_inv' : a ∈ s⁻¹ ↔ a⁻¹ ∈ s := by simp [Finset.mem_inv, inv_eq_iff_eq_inv]

