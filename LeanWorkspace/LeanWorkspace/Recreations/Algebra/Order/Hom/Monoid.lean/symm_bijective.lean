import Mathlib

variable {F α β γ δ : Type*}

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [Mul α] [Mul β]
  [Mul γ] [Mul δ] {f g : α ≃*o β}

theorem symm_bijective : Function.Bijective (OrderMonoidIso.symm : (α ≃*o β) → β ≃*o α) := Function.bijective_iff_has_inverse.mpr ⟨_, OrderMonoidIso.symm_symm, OrderMonoidIso.symm_symm⟩

