import Mathlib

variable {F α β γ : Type*}

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β}

theorem coe_id : ⇑(RingHom.id α) = _root_.id := rfl

