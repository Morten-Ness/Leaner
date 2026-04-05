import Mathlib

variable {F α β γ δ : Type*}

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [Mul α] [Mul β]
  [Mul γ] [Mul δ] {f g : α ≃*o β}

theorem cancel_left {g : α ≃*o β} {f₁ f₂ : β ≃*o γ} (hg : Function.Surjective g) :
    g.trans f₁ = g.trans f₂ ↔ f₁ = f₂ := ⟨fun h => OrderMonoidIso.ext <| hg.forall.2 <| DFunLike.ext_iff.1 h, fun _ => by congr⟩

