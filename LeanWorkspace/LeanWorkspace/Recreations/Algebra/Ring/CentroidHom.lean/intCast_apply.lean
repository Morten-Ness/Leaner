import Mathlib

variable {F M N R α : Type*}

variable [NonUnitalNonAssocRing α]

theorem intCast_apply (z : ℤ) (m : α) : (z : CentroidHom α) m = z • m := rfl

