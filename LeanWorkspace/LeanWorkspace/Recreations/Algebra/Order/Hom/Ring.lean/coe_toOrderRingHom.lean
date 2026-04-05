import Mathlib

variable {F α β γ δ : Type*}

variable [NonAssocSemiring α] [Preorder α] [NonAssocSemiring β] [Preorder β]

theorem coe_toOrderRingHom (f : α ≃+*o β) : ⇑(f : α →+*o β) = f := rfl

