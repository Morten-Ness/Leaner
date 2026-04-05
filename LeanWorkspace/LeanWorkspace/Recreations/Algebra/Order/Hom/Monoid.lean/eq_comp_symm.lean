import Mathlib

variable {F α β γ δ : Type*}

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [Mul α] [Mul β]
  [Mul γ] [Mul δ] {f g : α ≃*o β}

theorem eq_comp_symm (e : α ≃*o β) (f : β → α) (g : α → α) :
    f = g ∘ e.symm ↔ f ∘ e = g := e.toEquiv.eq_comp_symm f g

