import Mathlib

variable {F α β γ δ : Type*}

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [MulOneClass α] [MulOneClass β]
  [MulOneClass γ] [MulOneClass δ] {f g : α →*o β}

theorem coe_comp_monoidHom (f : β →*o γ) (g : α →*o β) :
    (f.comp g : α →* γ) = (f : β →* γ).comp g := rfl

