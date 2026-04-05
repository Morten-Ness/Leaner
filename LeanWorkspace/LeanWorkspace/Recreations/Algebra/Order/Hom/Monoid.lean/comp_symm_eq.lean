import Mathlib

variable {F α β γ δ : Type*}

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [Mul α] [Mul β]
  [Mul γ] [Mul δ] {f g : α ≃*o β}

theorem comp_symm_eq (e : α ≃*o β) (f : β → α) (g : α → α) :
    g ∘ e.symm = f ↔ g = f ∘ e := e.toEquiv.comp_symm_eq f g

