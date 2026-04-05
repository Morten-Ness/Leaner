import Mathlib

variable {R : Type u}

theorem mul_self_eq_mul_self_iff [NonUnitalNonAssocRing R] [NoZeroDivisors R] {a b : R}
    (h : Commute a b) : a * a = b * b ↔ a = b ∨ a = -b := by
  rw [← sub_eq_zero, Commute.mul_self_sub_mul_self_eq h, mul_eq_zero, or_comm, sub_eq_zero,
    add_eq_zero_iff_eq_neg]

