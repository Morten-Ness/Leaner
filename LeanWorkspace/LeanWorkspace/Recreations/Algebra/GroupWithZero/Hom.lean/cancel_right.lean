import Mathlib

variable {F α β γ δ M₀ : Type*} [MulZeroOneClass α] [MulZeroOneClass β] [MulZeroOneClass γ]
  [MulZeroOneClass δ]

variable [FunLike F α β]

theorem cancel_right {g₁ g₂ : β →*₀ γ} {f : α →*₀ β} (hf : Function.Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ := ⟨fun h ↦ ext <| hf.forall.2 (DFunLike.ext_iff.1 h), fun h ↦ h ▸ rfl⟩

