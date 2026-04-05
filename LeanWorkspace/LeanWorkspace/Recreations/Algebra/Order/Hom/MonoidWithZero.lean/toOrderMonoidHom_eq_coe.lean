import Mathlib

variable {F α β γ δ : Type*}

variable {hα : Preorder α} {hα' : MulZeroOneClass α} {hβ : Preorder β} {hβ' : MulZeroOneClass β}
  {hγ : Preorder γ} {hγ' : MulZeroOneClass γ}

theorem toOrderMonoidHom_eq_coe (f : α →*₀o β) : f.toOrderMonoidHom = f := rfl

