import Mathlib

variable {R : Type u}

theorem mul_self_eq_one_iff [NonAssocRing R] [NoZeroDivisors R] {a : R} :
    a * a = 1 ↔ a = 1 ∨ a = -1 := by
  rw [← mul_self_eq_mul_self_iff (Commute.one_right a), mul_one]

