import Mathlib

variable {F α β γ δ M₀ : Type*} [MulZeroOneClass α] [MulZeroOneClass β] [MulZeroOneClass γ]
  [MulZeroOneClass δ]

variable [FunLike F α β]

theorem coe_copy (f : α →*₀ β) (f' : α → β) (h) : (f.copy f' h) = f' := rfl

