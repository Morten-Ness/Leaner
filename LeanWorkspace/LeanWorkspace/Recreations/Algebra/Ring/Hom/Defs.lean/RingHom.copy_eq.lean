import Mathlib

variable {F α β γ : Type*}

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β}

theorem copy_eq (f : α →+* β) (f' : α → β) (h : f' = f) : f.copy f' h = f := DFunLike.ext' h

