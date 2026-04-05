import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [InvolutiveInv α] {s : Finset α} {a : α}

theorem inv_inter (s t : Finset α) : (s ∩ t)⁻¹ = s⁻¹ ∩ t⁻¹ := coe_injective <| by simp

