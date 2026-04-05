import Mathlib

variable {F α β γ : Type*}

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β}

theorem toMonoidHom_eq_coe (f : α →+* β) : f.toMonoidHom = f := rfl

