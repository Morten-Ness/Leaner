import Mathlib

variable {F α β γ δ : Type*}

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [MulOneClass α] [MulOneClass β]
  [MulOneClass γ] [MulOneClass δ] {f g : α →*o β}

theorem comp_assoc (f : γ →*o δ) (g : β →*o γ) (h : α →*o β) :
    (f.comp g).comp h = f.comp (g.comp h) := rfl

