import Mathlib

variable {F M N R α : Type*}

variable [NonUnitalNonAssocRing α]

theorem coe_neg (f : CentroidHom α) : ⇑(-f) = -f := rfl

