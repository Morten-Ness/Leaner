import Mathlib

variable {M R : Type*}

variable [Monoid M] [Ring R] [MulSemiringAction M R]

theorem smul_sup (a : M) (S T : Subring R) : a • (S ⊔ T) = a • S ⊔ a • T := map_sup _ _ _

