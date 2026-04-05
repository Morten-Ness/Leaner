import Mathlib

variable {R : Type u}

variable [Ring R] [PartialOrder R] [IsOrderedRing R] {a b c : R}

theorem one_sub_le_one_add_mul_one_sub (h : c + b * c ≤ a + b) : 1 - a ≤ (1 + b) * (1 - c) := by
  rw [mul_one_sub, one_add_mul, sub_le_sub_iff, add_assoc, add_comm b]
  gcongr

