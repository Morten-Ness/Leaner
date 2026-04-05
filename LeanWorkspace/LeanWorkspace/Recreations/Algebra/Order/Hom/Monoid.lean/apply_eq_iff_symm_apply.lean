import Mathlib

variable {F α β γ δ : Type*}

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [Mul α] [Mul β]
  [Mul γ] [Mul δ] {f g : α ≃*o β}

theorem apply_eq_iff_symm_apply (e : α ≃*o β) {x : α} {y : β} : e x = y ↔ x = e.symm y := e.toEquiv.apply_eq_iff_eq_symm_apply

