import Mathlib

variable {F α β γ δ : Type*}

variable [NonAssocSemiring α] [Preorder α] [NonAssocSemiring β] [Preorder β]

theorem toOrderRingHom_injective : Function.Injective (OrderRingIso.toOrderRingHom : α ≃+*o β → α →+*o β) := fun f g h => DFunLike.coe_injective <| by convert DFunLike.ext'_iff.1 h using 0

