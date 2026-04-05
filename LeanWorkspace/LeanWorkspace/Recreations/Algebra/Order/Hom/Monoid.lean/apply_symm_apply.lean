import Mathlib

variable {F α β γ δ : Type*}

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [Mul α] [Mul β]
  [Mul γ] [Mul δ] {f g : α ≃*o β}

theorem apply_symm_apply (e : α ≃*o β) (y : β) : e (e.symm y) = y := e.toEquiv.apply_symm_apply y

