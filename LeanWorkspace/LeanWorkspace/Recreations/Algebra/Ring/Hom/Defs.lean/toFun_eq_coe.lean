import Mathlib

variable {F α β γ : Type*}

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β}

theorem toFun_eq_coe (f : α →+* β) : f.toFun = f := rfl

