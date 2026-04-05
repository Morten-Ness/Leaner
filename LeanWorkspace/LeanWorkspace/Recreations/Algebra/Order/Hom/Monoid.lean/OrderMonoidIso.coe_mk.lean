import Mathlib

variable {F α β γ δ : Type*}

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [Mul α] [Mul β]
  [Mul γ] [Mul δ] {f g : α ≃*o β}

theorem coe_mk (f : α ≃* β) (h) : (OrderMonoidIso.mk f h : α → β) = f := rfl

