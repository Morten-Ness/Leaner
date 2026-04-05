import Mathlib

variable {F α β γ : Type*}

variable [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β]

theorem coe_mulHom_id : (NonUnitalRingHom.id α : α →ₙ* α) = MulHom.id α := rfl

