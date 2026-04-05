import Mathlib

variable {F α β γ : Type*}

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β}

theorem coe_monoidHom_id : (RingHom.id α : α →* α) = MonoidHom.id α := rfl

