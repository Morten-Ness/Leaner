import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [InvolutiveInv α] {s : Finset α} {a : α}

theorem inv_univ [Fintype α] : (univ : Finset α)⁻¹ = univ := by ext; simp

