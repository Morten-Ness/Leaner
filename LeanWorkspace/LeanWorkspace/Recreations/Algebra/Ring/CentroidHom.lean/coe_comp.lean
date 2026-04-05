import Mathlib

variable {F M N R α : Type*}

variable [NonUnitalNonAssocSemiring α]

theorem coe_comp (g f : CentroidHom α) : ⇑(g.comp f) = g ∘ f := rfl

