import Mathlib

variable {F A B C D : Type*}

variable [Monoid A] [Star A] [Monoid B] [Star B]

theorem copy_eq (f : A →⋆* B) (f' : A → B) (h : f' = f) : f.copy f' h = f := DFunLike.ext' h

