import Mathlib

variable {F M N R α : Type*}

variable [NonUnitalNonAssocSemiring α]

theorem coe_comp_addMonoidHom (g f : CentroidHom α) : (g.comp f : α →+ α) = (g : α →+ α).comp f := rfl

