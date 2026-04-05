import Mathlib

variable {F α β γ : Type*}

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β}

variable {_ : NonAssocSemiring γ}

theorem mul_def (f g : α →+* α) : f * g = f.comp g := rfl

