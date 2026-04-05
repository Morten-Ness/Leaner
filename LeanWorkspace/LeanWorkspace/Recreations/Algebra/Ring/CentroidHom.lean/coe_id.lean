import Mathlib

variable {F M N R α : Type*}

variable [NonUnitalNonAssocSemiring α]

theorem coe_id : ⇑(CentroidHom.id α) = id := rfl

