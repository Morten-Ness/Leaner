import Mathlib

variable {M R : Type*}

variable [Monoid M] [Ring R] [MulSemiringAction M R]

theorem smul_bot (a : M) : a • (⊥ : Subring R) = ⊥ := map_bot _

