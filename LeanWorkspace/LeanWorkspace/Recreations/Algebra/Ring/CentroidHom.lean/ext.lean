import Mathlib

variable {F M N R α : Type*}

variable [NonUnitalNonAssocSemiring α]

theorem ext {f g : CentroidHom α} (h : ∀ a, f a = g a) : f = g := DFunLike.ext f g h

