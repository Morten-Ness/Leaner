import Mathlib

variable {F α β γ δ : Type*}

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [Mul α] [Mul β]
  [Mul γ] [Mul δ] {f g : α ≃*o β}

theorem lt_symm_apply (e : α ≃*o β) {x : α} {y : β} : x < e.symm y ↔ e x < y := e.toOrderIso.lt_symm_apply

