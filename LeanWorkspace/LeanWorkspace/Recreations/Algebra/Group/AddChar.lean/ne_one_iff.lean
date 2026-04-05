import Mathlib

variable {A B M N : Type*} [AddMonoid A] [AddMonoid B] [Monoid M] [Monoid N] {ψ : AddChar A M}

theorem ne_one_iff : ψ ≠ 1 ↔ ∃ x, ψ x ≠ 1 := DFunLike.ne_iff

