import Mathlib

variable {F α β γ δ : Type*}

variable [NonAssocSemiring α] [Preorder α]

variable [NonAssocSemiring β] [Preorder β] [NonAssocSemiring γ] [Preorder γ] [NonAssocSemiring δ]
  [Preorder δ]

theorem coe_orderMonoidWithZeroHom_apply (f : α →+*o β) (a : α) : (f : α →*₀o β) a = f a := rfl

