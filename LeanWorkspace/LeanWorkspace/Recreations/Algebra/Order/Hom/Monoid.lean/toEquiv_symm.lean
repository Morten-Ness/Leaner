import Mathlib

variable {F α β γ δ : Type*}

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [Mul α] [Mul β]
  [Mul γ] [Mul δ] {f g : α ≃*o β}

theorem toEquiv_symm (f : α ≃*o β) : (f.symm : β ≃ α) = (f : α ≃ β).symm := rfl

