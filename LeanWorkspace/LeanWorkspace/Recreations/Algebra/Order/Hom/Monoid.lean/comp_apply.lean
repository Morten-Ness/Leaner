import Mathlib

variable {F α β γ δ : Type*}

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [MulOneClass α] [MulOneClass β]
  [MulOneClass γ] [MulOneClass δ] {f g : α →*o β}

theorem comp_apply (f : β →*o γ) (g : α →*o β) (a : α) : (f.comp g) a = f (g a) := rfl

