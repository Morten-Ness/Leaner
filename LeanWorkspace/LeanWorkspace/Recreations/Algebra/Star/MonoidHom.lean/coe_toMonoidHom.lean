import Mathlib

variable {F A B C D : Type*}

variable [Monoid A] [Star A] [Monoid B] [Star B]

theorem coe_toMonoidHom (f : A →⋆* B) : ⇑f.toMonoidHom = f := rfl

