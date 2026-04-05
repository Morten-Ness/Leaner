import Mathlib

variable {F M N R α : Type*}

variable [NonUnitalNonAssocRing α]

theorem neg_apply (f : CentroidHom α) (a : α) : (-f) a = -f a := rfl

