import Mathlib

variable {F α β γ δ : Type*}

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [MulOneClass α] [MulOneClass β]
  [MulOneClass γ] [MulOneClass δ] {f g : α →*o β}

theorem toMonoidHom_injective : Function.Injective (toMonoidHom : _ → α →* β) := fun f g h =>
  OrderMonoidHom.ext <| by convert DFunLike.ext_iff.1 h using 0

