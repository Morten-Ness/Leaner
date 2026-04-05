import Mathlib

variable {F M N R α : Type*}

variable [NonUnitalNonAssocRing α]

theorem toEnd_sub (x y : CentroidHom α) : (x - y).toEnd = x.toEnd - y.toEnd := rfl

