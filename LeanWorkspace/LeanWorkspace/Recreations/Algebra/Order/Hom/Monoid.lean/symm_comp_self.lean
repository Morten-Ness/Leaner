import Mathlib

variable {F α β γ δ : Type*}

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [Mul α] [Mul β]
  [Mul γ] [Mul δ] {f g : α ≃*o β}

theorem symm_comp_self (e : α ≃*o β) : e.symm ∘ e = id := funext OrderMonoidIso.symm_apply_apply e

