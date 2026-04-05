import Mathlib

variable {F M N R α : Type*}

variable [NonUnitalNonAssocSemiring α]

theorem toFun_eq_coe {f : CentroidHom α} : f.toFun = f := rfl

