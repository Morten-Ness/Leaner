import Mathlib

variable {F α β γ δ : Type*}

variable {hα : Preorder α} {hα' : MulZeroOneClass α} {hβ : Preorder β} {hβ' : MulZeroOneClass β}
  {hγ : Preorder γ} {hγ' : MulZeroOneClass γ}

theorem toMonoidWithZeroHom_coe (f : β →*₀o γ) (g : α →*₀o β) :
    (f.comp g : α →*₀ γ) = (f : β →*₀ γ).comp g := rfl

