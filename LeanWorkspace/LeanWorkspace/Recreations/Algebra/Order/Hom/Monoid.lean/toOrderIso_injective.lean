import Mathlib

variable {F α β γ δ : Type*}

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [Mul α] [Mul β]
  [Mul γ] [Mul δ] {f g : α ≃*o β}

theorem toOrderIso_injective : Function.Injective (OrderMonoidIso.toOrderIso : _ → α ≃o β) := fun f g h =>
  OrderMonoidIso.ext <| by convert DFunLike.ext_iff.1 h using 0

