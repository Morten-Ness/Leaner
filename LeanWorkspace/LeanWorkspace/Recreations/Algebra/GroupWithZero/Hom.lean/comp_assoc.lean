import Mathlib

variable {F α β γ δ M₀ : Type*} [MulZeroOneClass α] [MulZeroOneClass β] [MulZeroOneClass γ]
  [MulZeroOneClass δ]

variable [FunLike F α β]

theorem comp_assoc (f : α →*₀ β) (g : β →*₀ γ) (h : γ →*₀ δ) :
    (h.comp g).comp f = h.comp (g.comp f) := rfl

