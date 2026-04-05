import Mathlib

variable {F α β γ δ : Type*}

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [MulZeroOneClass α] [MulZeroOneClass β]
  [MulZeroOneClass γ] [MulZeroOneClass δ] {f g : α →*₀o β}

theorem coe_comp_monoidWithZeroHom (f : β →*₀o γ) (g : α →*₀o β) :
    (f.comp g : α →*₀ γ) = (f : β →*₀ γ).comp g := rfl

