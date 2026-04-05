import Mathlib

variable {F α β γ : Type*}

variable [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β]

variable [NonUnitalNonAssocSemiring γ]

theorem comp_id (f : α →ₙ+* β) : f.comp (NonUnitalRingHom.id α) = f := NonUnitalRingHom.ext fun _ => rfl

