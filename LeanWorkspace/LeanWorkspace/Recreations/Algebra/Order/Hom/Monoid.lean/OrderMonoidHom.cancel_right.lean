import Mathlib

variable {F α β γ δ : Type*}

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [MulOneClass α] [MulOneClass β]
  [MulOneClass γ] [MulOneClass δ] {f g : α →*o β}

theorem cancel_right {g₁ g₂ : β →*o γ} {f : α →*o β} (hf : Function.Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ := ⟨fun h => OrderMonoidHom.ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, fun _ => by congr⟩

