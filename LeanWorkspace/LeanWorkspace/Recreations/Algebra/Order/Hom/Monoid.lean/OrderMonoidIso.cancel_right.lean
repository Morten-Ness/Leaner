import Mathlib

variable {F α β γ δ : Type*}

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [Mul α] [Mul β]
  [Mul γ] [Mul δ] {f g : α ≃*o β}

theorem cancel_right {g₁ g₂ : α ≃*o β} {f : β ≃*o γ} (hf : Function.Injective f) :
    g₁.trans f = g₂.trans f ↔ g₁ = g₂ := ⟨fun h => OrderMonoidIso.ext fun a => hf <| by rw [← OrderMonoidIso.trans_apply, h, OrderMonoidIso.trans_apply], by rintro rfl; rfl⟩

