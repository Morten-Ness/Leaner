import Mathlib

variable {F α β γ δ : Type*}

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [Mul α] [Mul β]
  [Mul γ] [Mul δ] {f g : α ≃*o β}

theorem symm_apply_eq (e : α ≃*o β) {x y} : e.symm x = y ↔ x = e y := e.toEquiv.symm_apply_eq

