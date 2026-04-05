import Mathlib

variable {F α β γ δ : Type*}

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [Mul α] [Mul β]
  [Mul γ] [Mul δ] {f g : α ≃*o β}

theorem mk_coe (f : α ≃*o β) (h) : OrderMonoidIso.mk (f : α ≃* β) h = f := rfl

