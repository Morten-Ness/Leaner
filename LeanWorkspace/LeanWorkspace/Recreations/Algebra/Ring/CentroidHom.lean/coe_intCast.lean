import Mathlib

variable {F M N R α : Type*}

variable [NonUnitalNonAssocRing α]

theorem coe_intCast (z : ℤ) : ⇑(z : CentroidHom α) = z • (CentroidHom.id α) := rfl

