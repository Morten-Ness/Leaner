import Mathlib

variable {F α β γ : Type*}

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β}

theorem coe_addMonoidHom_id : (RingHom.id α : α →+ α) = AddMonoidHom.id α := rfl

