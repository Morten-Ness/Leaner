import Mathlib

variable {R : Type*}

variable [NonAssocRing R] {a : R}

theorem _root_.isIdempotentElem_iff_mul_one_sub_self :
    IsIdempotentElem a ↔ a * (1 - a) = 0 := by
  rw [mul_sub, mul_one, sub_eq_zero, eq_comm, IsIdempotentElem]

