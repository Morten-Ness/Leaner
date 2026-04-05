import Mathlib

variable {F A B C D : Type*}

variable [Monoid A] [Star A] [Monoid B] [Star B]

variable [Monoid C] [Star C] [Monoid D] [Star D]

theorem comp_assoc (f : C →⋆* D) (g : B →⋆* C) (h : A →⋆* B) :
    (f.comp g).comp h = f.comp (g.comp h) := rfl

