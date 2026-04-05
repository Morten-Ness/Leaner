import Mathlib

variable {F α β γ δ M₀ : Type*} [MulZeroOneClass α] [MulZeroOneClass β] [MulZeroOneClass γ]
  [MulZeroOneClass δ]

variable [FunLike F α β]

theorem toZeroHom_injective : Function.Injective (toZeroHom : (α →*₀ β) → ZeroHom α β) := Function.Injective.of_comp (f := DFunLike.coe) DFunLike.coe_injective

