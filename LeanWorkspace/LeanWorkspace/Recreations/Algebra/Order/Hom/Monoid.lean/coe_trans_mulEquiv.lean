import Mathlib

variable {F α β γ δ : Type*}

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [Mul α] [Mul β]
  [Mul γ] [Mul δ] {f g : α ≃*o β}

theorem coe_trans_mulEquiv (f : α ≃*o β) (g : β ≃*o γ) :
    (f.trans g : α ≃* γ) = (f : α ≃* β).trans g := rfl

