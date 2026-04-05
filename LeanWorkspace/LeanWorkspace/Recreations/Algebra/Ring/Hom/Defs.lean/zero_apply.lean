import Mathlib

variable {F α β γ : Type*}

variable [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β]

theorem zero_apply (x : α) : (0 : α →ₙ+* β) x = 0 := rfl

