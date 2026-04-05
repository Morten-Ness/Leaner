import Mathlib

variable {F M N R α : Type*}

variable [NonUnitalNonAssocSemiring α]

theorem coe_copy (f : CentroidHom α) (f' : α → α) (h : f' = f) : ⇑(f.copy f' h) = f' := rfl

