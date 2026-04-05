import Mathlib

variable {F A B C D : Type*}

variable [Monoid A] [Star A] [Monoid B] [Star B]

theorem ext {f g : A →⋆* B} (h : ∀ x, f x = g x) : f = g := DFunLike.ext _ _ h

