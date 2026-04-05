import Mathlib

variable {F α β γ : Type*}

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β}

variable {_ : NonAssocSemiring γ}

theorem id_comp (f : α →+* β) : (RingHom.id β).comp f = f := RingHom.ext fun _ => rfl

