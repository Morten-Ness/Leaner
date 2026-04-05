import Mathlib

variable {F α β γ δ : Type*}

variable [NonAssocSemiring α] [Preorder α]

variable [NonAssocSemiring β] [Preorder β] [NonAssocSemiring γ] [Preorder γ] [NonAssocSemiring δ]
  [Preorder δ]

theorem coe_orderMonoidWithZeroHom_id :
    (OrderRingHom.id α : α →*₀o α) = OrderMonoidWithZeroHom.id α := rfl

