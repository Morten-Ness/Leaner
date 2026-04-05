import Mathlib

variable {F α β γ δ : Type*}

variable {hα : Preorder α} {hα' : MulZeroOneClass α} {hβ : Preorder β} {hβ' : MulZeroOneClass β}
  {hγ : Preorder γ} {hγ' : MulZeroOneClass γ}

theorem toMonoidWithZeroHom_mk (f : α →*₀ β) (hf : Monotone f) :
    ((OrderMonoidWithZeroHom.mk f hf) : α →*₀ β) = f := by
  rfl

