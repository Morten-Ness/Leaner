import Mathlib

variable {A B M N : Type*} [AddMonoid A] [AddMonoid B] [Monoid M] [Monoid N] {ψ : AddChar A M}

theorem eq_zero_iff : ψ = 0 ↔ ∀ x, ψ x = 1 := DFunLike.ext_iff

