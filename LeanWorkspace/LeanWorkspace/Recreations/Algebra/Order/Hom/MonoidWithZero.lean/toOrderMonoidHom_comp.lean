import Mathlib

variable {F α β γ δ : Type*}

variable {hα : Preorder α} {hα' : MulZeroOneClass α} {hβ : Preorder β} {hβ' : MulZeroOneClass β}
  {hγ : Preorder γ} {hγ' : MulZeroOneClass γ}

theorem toOrderMonoidHom_comp (f : β →*₀o γ) (g : α →*₀o β) :
    (f.comp g : α →*o γ) = (f : β →*o γ).comp g := rfl

