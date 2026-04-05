import Mathlib

variable {F α β γ δ M₀ : Type*} [MulZeroOneClass α] [MulZeroOneClass β] [MulZeroOneClass γ]
  [MulZeroOneClass δ]

variable [FunLike F α β]

theorem comp_apply (g : β →*₀ γ) (f : α →*₀ β) (x : α) : g.comp f x = g (f x) := rfl

