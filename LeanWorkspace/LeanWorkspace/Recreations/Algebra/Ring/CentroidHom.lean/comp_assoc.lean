import Mathlib

variable {F M N R α : Type*}

variable [NonUnitalNonAssocSemiring α]

theorem comp_assoc (h g f : CentroidHom α) : (h.comp g).comp f = h.comp (g.comp f) := rfl

