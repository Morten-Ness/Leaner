import Mathlib

variable {F M N R α : Type*}

variable [NonUnitalNonAssocRing α]

theorem toEnd_intCast (z : ℤ) : (z : CentroidHom α).toEnd = ↑z := rfl

