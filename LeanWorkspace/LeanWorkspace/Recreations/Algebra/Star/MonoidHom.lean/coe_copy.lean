import Mathlib

variable {F A B C D : Type*}

variable [Monoid A] [Star A] [Monoid B] [Star B]

theorem coe_copy (f : A →⋆* B) (f' : A → B) (h : f' = f) : ⇑(f.copy f' h) = f' := rfl

