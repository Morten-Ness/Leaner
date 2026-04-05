import Mathlib

variable {F α β γ δ : Type*}

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [MulZeroOneClass α] [MulZeroOneClass β]
  [MulZeroOneClass γ] [MulZeroOneClass δ] {f g : α →*₀o β}

theorem comp_apply (f : β →*₀o γ) (g : α →*₀o β) (a : α) : (f.comp g) a = f (g a) := rfl

