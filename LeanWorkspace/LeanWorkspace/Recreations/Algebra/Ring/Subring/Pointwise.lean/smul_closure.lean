import Mathlib

variable {M R : Type*}

variable [Monoid M] [Ring R] [MulSemiringAction M R]

theorem smul_closure (a : M) (s : Set R) : a • closure s = closure (a • s) := RingHom.map_closure _ _

