import Mathlib

variable {F α β γ δ : Type*}

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [MulZeroOneClass α] [MulZeroOneClass β]
  [MulZeroOneClass γ] [MulZeroOneClass δ] {f g : α →*₀o β}

theorem comp_assoc (f : γ →*₀o δ) (g : β →*₀o γ) (h : α →*₀o β) :
    (f.comp g).comp h = f.comp (g.comp h) := rfl

