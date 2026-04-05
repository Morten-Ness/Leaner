import Mathlib

variable {F α β γ : Type*}

variable [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β]

variable [NonUnitalNonAssocSemiring γ]

theorem comp_assoc {δ} {_ : NonUnitalNonAssocSemiring δ} (f : α →ₙ+* β) (g : β →ₙ+* γ)
    (h : γ →ₙ+* δ) : (h.comp g).comp f = h.comp (g.comp f) := rfl

