import Mathlib

variable {R : Type u}

theorem mul_self_sub_one [NonAssocRing R] (a : R) : a * a - 1 = (a + 1) * (a - 1) := by
  rw [← Commute.mul_self_sub_mul_self_eq (Commute.one_right a), mul_one]

