import Mathlib

variable {M R : Type*}

variable [Monoid M] [Semiring R] [MulSemiringAction M R]

theorem smul_bot (a : M) : a • (⊥ : Subsemiring R) = ⊥ := map_bot _

