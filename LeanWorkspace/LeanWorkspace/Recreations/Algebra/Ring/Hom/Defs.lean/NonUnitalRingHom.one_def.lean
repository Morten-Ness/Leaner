import Mathlib

variable {F α β γ : Type*}

variable [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β]

variable [NonUnitalNonAssocSemiring γ]

theorem one_def : (1 : α →ₙ+* α) = NonUnitalRingHom.id α := rfl

