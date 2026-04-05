import Mathlib

variable {F M N R α : Type*}

variable [NonUnitalNonAssocSemiring α]

theorem id_apply (a : α) : CentroidHom.id α a = a := rfl

