import Mathlib

variable {F M N R α : Type*}

variable [NonUnitalNonAssocSemiring α]

theorem toAddMonoidHom_eq_coe (f : CentroidHom α) : f.toAddMonoidHom = f := rfl

