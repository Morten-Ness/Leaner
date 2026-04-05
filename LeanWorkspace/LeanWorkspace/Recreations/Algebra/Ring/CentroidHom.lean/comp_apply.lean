import Mathlib

variable {F M N R α : Type*}

variable [NonUnitalNonAssocSemiring α]

theorem comp_apply (g f : CentroidHom α) (a : α) : g.comp f a = g (f a) := rfl

