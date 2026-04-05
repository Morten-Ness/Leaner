import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [InvolutiveInv α] {s : Finset α} {a : α}

theorem inv_filter_univ (p : α → Prop) [Fintype α] [DecidablePred p] :
    ({x | p x} : Finset α)⁻¹ = {x | p x⁻¹} := by
  simp

