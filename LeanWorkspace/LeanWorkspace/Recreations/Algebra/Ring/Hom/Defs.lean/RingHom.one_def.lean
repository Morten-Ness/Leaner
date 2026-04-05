import Mathlib

variable {F α β γ : Type*}

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β}

variable {_ : NonAssocSemiring γ}

theorem one_def : (1 : α →+* α) = RingHom.id α := rfl

