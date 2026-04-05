import Mathlib

variable {F α β γ δ : Type*}

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [Mul α] [Mul β]
  [Mul γ] [Mul δ] {f g : α ≃*o β}

theorem symm_comp_eq (e : α ≃*o β) (f : α → α) (g : α → β) :
    e.symm ∘ g = f ↔ g = e ∘ f := e.toEquiv.symm_comp_eq f g

