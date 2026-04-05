import Mathlib

variable {F α β γ δ : Type*}

variable [NonAssocSemiring α] [Preorder α]

variable [NonAssocSemiring β] [Preorder β] [NonAssocSemiring γ] [Preorder γ] [NonAssocSemiring δ]
  [Preorder δ]

theorem coe_coe_orderAddMonoidHom (f : α →+*o β) : ⇑(f : α →+o β) = f := rfl

