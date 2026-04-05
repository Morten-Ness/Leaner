import Mathlib

variable {R : Type*} [Semiring R] [LinearOrder R] [IsStrictOrderedRing R] {a : R}

theorem invOf_le_one [Invertible a] (h : 1 ≤ a) : ⅟a ≤ 1 := mul_invOf_self a ▸ le_mul_of_one_le_left (invOf_nonneg.2 <| zero_le_one.trans h) h

