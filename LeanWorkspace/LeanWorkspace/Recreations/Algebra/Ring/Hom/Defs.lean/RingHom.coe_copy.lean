import Mathlib

variable {F α β γ : Type*}

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β}

theorem coe_copy (f : α →+* β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' := rfl

