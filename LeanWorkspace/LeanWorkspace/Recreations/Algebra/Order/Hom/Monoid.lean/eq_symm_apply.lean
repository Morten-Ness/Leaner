import Mathlib

variable {F α β γ δ : Type*}

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [Mul α] [Mul β]
  [Mul γ] [Mul δ] {f g : α ≃*o β}

theorem eq_symm_apply (e : α ≃*o β) {x y} : y = e.symm x ↔ e y = x := e.toEquiv.eq_symm_apply

