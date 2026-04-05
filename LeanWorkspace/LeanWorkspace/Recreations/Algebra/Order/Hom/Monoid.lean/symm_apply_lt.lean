import Mathlib

variable {F α β γ δ : Type*}

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [Mul α] [Mul β]
  [Mul γ] [Mul δ] {f g : α ≃*o β}

theorem symm_apply_lt (e : α ≃*o β) {x : α} {y : β} : e.symm y < x ↔ y < e x := e.toOrderIso.symm_apply_lt

