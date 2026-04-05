import Mathlib

variable {R : Type*}

variable [NonAssocRing R] {a : R}

theorem mul_one_sub_self (h : IsIdempotentElem a) : a * (1 - a) = 0 := by
  rw [mul_sub, mul_one, h.eq, sub_self]

