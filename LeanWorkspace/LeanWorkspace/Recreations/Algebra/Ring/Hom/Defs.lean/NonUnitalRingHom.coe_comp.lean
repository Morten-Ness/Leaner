import Mathlib

variable {F α β γ : Type*}

variable [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β]

variable [NonUnitalNonAssocSemiring γ]

theorem coe_comp (g : β →ₙ+* γ) (f : α →ₙ+* β) : ⇑(g.comp f) = g ∘ f := rfl

