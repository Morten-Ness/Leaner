import Mathlib

variable {F A B C D : Type*}

variable [Monoid A] [Star A] [Monoid B] [Star B]

variable [Monoid C] [Star C] [Monoid D] [Star D]

theorem one_apply (a : A) : (1 : A →⋆* A) a = a := rfl

