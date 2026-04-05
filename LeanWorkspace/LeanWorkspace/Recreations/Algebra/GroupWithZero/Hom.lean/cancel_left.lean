import Mathlib

variable {F α β γ δ M₀ : Type*} [MulZeroOneClass α] [MulZeroOneClass β] [MulZeroOneClass γ]
  [MulZeroOneClass δ]

variable [FunLike F α β]

theorem cancel_left {g : β →*₀ γ} {f₁ f₂ : α →*₀ β} (hg : Function.Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ := ⟨fun h ↦ ext fun x ↦ hg <| by rw [← MonoidWithZeroHom.comp_apply, h,
    MonoidWithZeroHom.comp_apply], fun h ↦ h ▸ rfl⟩

