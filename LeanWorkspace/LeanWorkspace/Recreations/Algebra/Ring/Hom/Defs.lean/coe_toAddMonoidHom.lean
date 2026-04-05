import Mathlib

variable {F α β γ : Type*}

variable [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β]

theorem coe_toAddMonoidHom (f : α →ₙ+* β) : ⇑f.toAddMonoidHom = f := rfl

