import Mathlib

variable {F M N R α : Type*}

variable [NonUnitalNonAssocSemiring α]

theorem toAddMonoidHom_id : (CentroidHom.id α : α →+ α) = AddMonoidHom.id α := rfl

