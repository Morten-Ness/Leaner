import Mathlib

variable {F α β γ : Type*}

variable [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β]

variable [NonUnitalNonAssocSemiring γ]

theorem zero_comp (f : α →ₙ+* β) : (0 : β →ₙ+* γ).comp f = 0 := by
  ext
  rfl

