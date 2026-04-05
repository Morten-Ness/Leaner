import Mathlib

variable {F α β γ δ : Type*}

variable [NonAssocSemiring α] [Preorder α] [NonAssocSemiring β] [Preorder β]

theorem toOrderRingHom_eq_coe (f : α ≃+*o β) : f.toOrderRingHom = f := rfl

