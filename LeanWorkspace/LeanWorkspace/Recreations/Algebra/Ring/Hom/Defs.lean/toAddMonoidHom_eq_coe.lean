import Mathlib

variable {F α β γ : Type*}

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β}

theorem toAddMonoidHom_eq_coe (f : α →+* β) : f.toAddMonoidHom = f := rfl

