import Mathlib

variable {F α β γ δ : Type*}

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [MulZeroOneClass α] [MulZeroOneClass β]
  [MulZeroOneClass γ] [MulZeroOneClass δ] {f g : α →*₀o β}

theorem cancel_left {g : β →*₀o γ} {f₁ f₂ : α →*₀o β} (hg : Function.Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ := ⟨fun h => OrderMonoidWithZeroHom.ext fun a => hg <| by rw [← OrderMonoidWithZeroHom.comp_apply, h, OrderMonoidWithZeroHom.comp_apply], congr_arg _⟩

