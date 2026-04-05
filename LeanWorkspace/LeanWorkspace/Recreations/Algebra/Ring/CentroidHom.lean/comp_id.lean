import Mathlib

variable {F M N R α : Type*}

variable [NonUnitalNonAssocSemiring α]

theorem comp_id (f : CentroidHom α) : f.comp (CentroidHom.id α) = f := rfl

