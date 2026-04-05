import Mathlib

variable {F α β γ δ M₀ : Type*} [MulZeroOneClass α] [MulZeroOneClass β] [MulZeroOneClass γ]
  [MulZeroOneClass δ]

variable [FunLike F α β]

theorem toMonoidHom_injective : Function.Injective (toMonoidHom : (α →*₀ β) → α →* β) := Function.Injective.of_comp (f := DFunLike.coe) DFunLike.coe_injective

