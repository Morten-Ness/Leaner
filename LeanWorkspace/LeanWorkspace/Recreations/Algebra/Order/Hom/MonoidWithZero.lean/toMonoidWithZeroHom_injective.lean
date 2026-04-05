import Mathlib

variable {F α β γ δ : Type*}

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [MulZeroOneClass α] [MulZeroOneClass β]
  [MulZeroOneClass γ] [MulZeroOneClass δ] {f g : α →*₀o β}

theorem toMonoidWithZeroHom_injective : Function.Injective (toMonoidWithZeroHom : _ → α →*₀ β) := fun f g h => OrderMonoidWithZeroHom.ext <| by convert DFunLike.ext_iff.1 h using 0

