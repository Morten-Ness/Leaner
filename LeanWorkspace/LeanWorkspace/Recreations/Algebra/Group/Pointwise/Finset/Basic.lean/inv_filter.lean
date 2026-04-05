import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [InvolutiveInv α] {s : Finset α} {a : α}

theorem inv_filter (s : Finset α) (p : α → Prop) [DecidablePred p] :
    ({x ∈ s | p x} : Finset α)⁻¹ = {x ∈ s⁻¹ | p x⁻¹} := by
  ext; simp

