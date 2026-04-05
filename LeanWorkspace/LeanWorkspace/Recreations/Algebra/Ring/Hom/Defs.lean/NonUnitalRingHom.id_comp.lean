import Mathlib

variable {F α β γ : Type*}

variable [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β]

variable [NonUnitalNonAssocSemiring γ]

theorem id_comp (f : α →ₙ+* β) : (NonUnitalRingHom.id β).comp f = f := NonUnitalRingHom.ext fun _ => rfl

