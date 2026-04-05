import Mathlib

variable {F α β γ : Type*}

variable [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β]

theorem coe_addMonoidHom_id : (NonUnitalRingHom.id α : α →+ α) = AddMonoidHom.id α := rfl

