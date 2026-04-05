import Mathlib

variable {F A B C D : Type*}

variable [Monoid A] [Star A] [Monoid B] [Star B]

variable [Monoid C] [Star C] [Monoid D] [Star D]

theorem comp_apply (f : B →⋆* C) (g : A →⋆* B) (a : A) : StarMonoidHom.comp f g a = f (g a) := rfl

