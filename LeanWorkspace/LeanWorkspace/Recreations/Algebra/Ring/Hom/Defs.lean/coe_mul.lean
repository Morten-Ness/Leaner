import Mathlib

variable {F α β γ : Type*}

variable [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β]

variable [NonUnitalNonAssocSemiring γ]

theorem coe_mul (f g : α →ₙ+* α) : ⇑(f * g) = f ∘ g := rfl

