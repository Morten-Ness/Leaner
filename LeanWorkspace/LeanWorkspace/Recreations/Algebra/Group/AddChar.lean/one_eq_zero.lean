import Mathlib

variable {A B M N : Type*} [AddMonoid A] [AddMonoid B] [Monoid M] [Monoid N] {ψ : AddChar A M}

theorem one_eq_zero : (1 : AddChar A M) = (0 : AddChar A M) := rfl

