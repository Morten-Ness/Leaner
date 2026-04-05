import Mathlib

variable {F α β γ : Type*}

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β}

theorem id_apply (x : α) : RingHom.id α x = x := rfl

