import Mathlib

variable {F α β γ δ : Type*}

variable [NonAssocSemiring α] [Preorder α]

variable [NonAssocSemiring β] [Preorder β] [NonAssocSemiring γ] [Preorder γ] [NonAssocSemiring δ]
  [Preorder δ]

theorem cancel_right {f₁ f₂ : β →+*o γ} {g : α →+*o β} (hg : Function.Surjective g) :
    f₁.comp g = f₂.comp g ↔ f₁ = f₂ := ⟨fun h => OrderRingHom.ext <| hg.forall.2 <| DFunLike.ext_iff.1 h, fun h => by rw [h]⟩

