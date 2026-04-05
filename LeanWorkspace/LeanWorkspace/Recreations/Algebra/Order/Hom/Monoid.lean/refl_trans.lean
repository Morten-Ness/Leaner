import Mathlib

variable {F α β γ δ : Type*}

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [Mul α] [Mul β]
  [Mul γ] [Mul δ] {f g : α ≃*o β}

theorem refl_trans (f : α ≃*o β) : (OrderMonoidIso.refl α).trans f = f := rfl

