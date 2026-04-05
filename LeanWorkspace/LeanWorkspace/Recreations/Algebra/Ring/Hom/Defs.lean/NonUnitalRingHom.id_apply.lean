import Mathlib

variable {F α β γ : Type*}

variable [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β]

theorem id_apply (x : α) : NonUnitalRingHom.id α x = x := rfl

