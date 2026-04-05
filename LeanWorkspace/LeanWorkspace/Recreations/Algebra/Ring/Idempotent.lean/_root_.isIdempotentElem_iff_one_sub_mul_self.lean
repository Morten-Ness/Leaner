import Mathlib

variable {R : Type*}

variable [NonAssocRing R] {a : R}

theorem _root_.isIdempotentElem_iff_one_sub_mul_self :
    IsIdempotentElem a ↔ (1 - a) * a = 0 := by
  rw [sub_mul, one_mul, sub_eq_zero, eq_comm, IsIdempotentElem]

