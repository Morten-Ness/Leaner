import Mathlib

variable {F M N R α : Type*}

variable [NonUnitalNonAssocSemiring α]

theorem coe_toAddMonoidHom (f : CentroidHom α) : ⇑(f : α →+ α) = f := rfl

