import Mathlib

variable {F α β γ : Type*}

variable [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β]

variable [NonUnitalNonAssocSemiring γ]

theorem comp_apply (g : β →ₙ+* γ) (f : α →ₙ+* β) (x : α) : g.comp f x = g (f x) := rfl

