import Mathlib

variable {R : Type*}

variable [NonUnitalRing R] {a b : R}

theorem add_sub_mul_of_commute (h : Commute a b) (ha : IsIdempotentElem a) (hb : IsIdempotentElem b) :
    IsIdempotentElem (a + b - a * b) := by
  simp only [IsIdempotentElem, h.eq, mul_sub, mul_add, sub_mul, add_mul, ha.eq,
    mul_assoc, add_sub_cancel_right, hb.eq, hb.mul_self_mul, add_sub_cancel_left, sub_right_inj]
  rw [← h.eq, ha.mul_self_mul, h.eq, hb.mul_self_mul, add_sub_cancel_right]

