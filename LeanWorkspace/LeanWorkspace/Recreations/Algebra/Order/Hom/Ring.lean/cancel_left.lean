import Mathlib

variable {F α β γ δ : Type*}

variable [NonAssocSemiring α] [Preorder α]

variable [NonAssocSemiring β] [Preorder β] [NonAssocSemiring γ] [Preorder γ] [NonAssocSemiring δ]
  [Preorder δ]

theorem cancel_left {f : β →+*o γ} {g₁ g₂ : α →+*o β} (hf : Function.Injective f) :
    f.comp g₁ = f.comp g₂ ↔ g₁ = g₂ := ⟨fun h => OrderRingHom.ext fun a => hf <| by rw [← OrderRingHom.comp_apply, h, OrderRingHom.comp_apply], congr_arg _⟩

