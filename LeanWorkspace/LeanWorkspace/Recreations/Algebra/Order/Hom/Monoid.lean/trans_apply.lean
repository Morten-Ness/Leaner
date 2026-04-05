import Mathlib

variable {F α β γ δ : Type*}

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [Mul α] [Mul β]
  [Mul γ] [Mul δ] {f g : α ≃*o β}

theorem trans_apply (f : α ≃*o β) (g : β ≃*o γ) (a : α) : (f.trans g) a = g (f a) := rfl

