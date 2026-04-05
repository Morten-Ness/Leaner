import Mathlib

variable {R : Type*}

variable {p q : R}

variable [NonAssocRing R]

theorem mul_one_sub_self [Star R] (hp : IsStarProjection p) : p * (1 - p) = 0 := hp.isIdempotentElem.mul_one_sub_self

