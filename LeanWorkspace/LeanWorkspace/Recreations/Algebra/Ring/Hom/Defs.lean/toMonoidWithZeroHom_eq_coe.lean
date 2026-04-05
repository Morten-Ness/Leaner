import Mathlib

variable {F α β γ : Type*}

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β}

theorem toMonoidWithZeroHom_eq_coe (f : α →+* β) : (f.toMonoidWithZeroHom : α → β) = f := by
  rfl

