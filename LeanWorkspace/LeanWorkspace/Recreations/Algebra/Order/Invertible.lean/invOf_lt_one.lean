import Mathlib

variable {R : Type*} [Semiring R] [LinearOrder R] [IsStrictOrderedRing R] {a : R}

theorem invOf_lt_one [Invertible a] (h : 1 < a) : ⅟a < 1 := mul_invOf_self a ▸ lt_mul_of_one_lt_left (invOf_pos.2 <| one_pos.trans h) h

