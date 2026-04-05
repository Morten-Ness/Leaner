import Mathlib

variable {F M N R α : Type*}

variable [NonUnitalNonAssocRing α]

theorem toEnd_neg (x : CentroidHom α) : (-x).toEnd = -x.toEnd := rfl

