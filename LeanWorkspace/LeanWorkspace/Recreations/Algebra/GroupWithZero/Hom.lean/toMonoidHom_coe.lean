import Mathlib

variable {F α β γ δ M₀ : Type*} [MulZeroOneClass α] [MulZeroOneClass β] [MulZeroOneClass γ]
  [MulZeroOneClass δ]

variable [FunLike F α β]

theorem toMonoidHom_coe (f : α →*₀ β) : f.toMonoidHom.toFun = f := rfl

