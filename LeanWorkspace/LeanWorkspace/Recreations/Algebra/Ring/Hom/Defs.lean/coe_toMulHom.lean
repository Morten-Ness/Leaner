import Mathlib

variable {F α β γ : Type*}

variable [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β]

theorem coe_toMulHom (f : α →ₙ+* β) : ⇑f.toMulHom = f := rfl

