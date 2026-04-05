import Mathlib

variable {F α β γ : Type*}

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β}

variable {_ : NonAssocSemiring γ}

theorem comp_id (f : α →+* β) : f.comp (RingHom.id α) = f := RingHom.ext fun _ => rfl

