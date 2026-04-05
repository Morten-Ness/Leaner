import Mathlib

variable {F α β γ : Type*}

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β}

variable {_ : NonAssocSemiring γ}

theorem comp_assoc {δ} {_ : NonAssocSemiring δ} (f : α →+* β) (g : β →+* γ) (h : γ →+* δ) :
    (h.comp g).comp f = h.comp (g.comp f) := rfl

