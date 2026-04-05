import Mathlib

variable {F α β γ δ : Type*}

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [MulOneClass α] [MulOneClass β]
  [MulOneClass γ] [MulOneClass δ] {f g : α →*o β}

theorem cancel_left {g : β →*o γ} {f₁ f₂ : α →*o β} (hg : Function.Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ := ⟨fun h => OrderMonoidHom.ext fun a => hg <| by rw [← OrderMonoidHom.comp_apply, h, OrderMonoidHom.comp_apply], congr_arg _⟩

