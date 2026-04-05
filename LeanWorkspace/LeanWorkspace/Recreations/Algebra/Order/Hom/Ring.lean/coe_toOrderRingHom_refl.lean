import Mathlib

variable {F α β γ δ : Type*}

variable [NonAssocSemiring α] [Preorder α] [NonAssocSemiring β] [Preorder β]

theorem coe_toOrderRingHom_refl : (OrderRingIso.refl α : α →+*o α) = OrderRingHom.id α := rfl

