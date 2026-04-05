import Mathlib

variable {F α β γ : Type*}

variable [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β]

theorem coe_copy (f : α →ₙ+* β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' := rfl

