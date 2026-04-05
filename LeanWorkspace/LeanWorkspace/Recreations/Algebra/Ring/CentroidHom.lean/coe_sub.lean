import Mathlib

variable {F M N R α : Type*}

variable [NonUnitalNonAssocRing α]

theorem coe_sub (f g : CentroidHom α) : ⇑(f - g) = f - g := rfl

