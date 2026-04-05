import Mathlib

variable {F α β γ : Type*}

variable [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β]

theorem mk_coe (f : α →ₙ+* β) (h₁ h₂ h₃) : NonUnitalRingHom.mk (MulHom.mk f h₁) h₂ h₃ = f := NonUnitalRingHom.ext fun _ => rfl

