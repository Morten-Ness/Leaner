import Mathlib

variable {F M N R α : Type*}

variable [NonUnitalNonAssocSemiring α]

theorem id_comp (f : CentroidHom α) : (CentroidHom.id α).comp f = f := rfl

