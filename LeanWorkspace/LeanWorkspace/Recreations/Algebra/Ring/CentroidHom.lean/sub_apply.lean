import Mathlib

variable {F M N R α : Type*}

variable [NonUnitalNonAssocRing α]

theorem sub_apply (f g : CentroidHom α) (a : α) : (f - g) a = f a - g a := rfl

