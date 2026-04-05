import Mathlib

variable {R : Type u}

theorem mul_self_sub_mul_self_eq' [NonUnitalNonAssocRing R] {a b : R} (h : Commute a b) :
    a * a - b * b = (a - b) * (a + b) := by
  rw [mul_add, sub_mul, sub_mul, h.eq, sub_add_sub_cancel]

