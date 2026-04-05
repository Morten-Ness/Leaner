import Mathlib

variable {R : Type*}

variable {p q : R}

variable [NonAssocRing R]

theorem one_sub_mul_self [Star R] (hp : IsStarProjection p) : (1 - p) * p = 0 := hp.isIdempotentElem.one_sub_mul_self

