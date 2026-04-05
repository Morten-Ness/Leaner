import Mathlib

variable {F α β γ δ : Type*}

variable {_ : Preorder α} {_ : Preorder β} {_ : MulOneClass α} {_ : MulOneClass β}

theorem toOrderHom_eq_coe (f : α →*o β) : f.toOrderHom = f := rfl

