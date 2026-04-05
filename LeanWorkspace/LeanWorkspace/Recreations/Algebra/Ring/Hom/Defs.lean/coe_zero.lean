import Mathlib

variable {F α β γ : Type*}

variable [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β]

theorem coe_zero : ⇑(0 : α →ₙ+* β) = 0 := rfl

