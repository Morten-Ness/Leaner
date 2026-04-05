import Mathlib

variable {R : Type*}

variable [NonAssocRing R] {a : R}

theorem one_sub_mul_self (h : IsIdempotentElem a) : (1 - a) * a = 0 := by
  rw [sub_mul, one_mul, h.eq, sub_self]

