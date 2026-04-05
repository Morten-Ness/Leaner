import Mathlib

variable {R : Type u}

variable [Ring R] [PartialOrder R] [IsOrderedRing R] {a b c : R}

theorem one_sub_le_one_sub_mul_one_add (h : b + b * c ≤ a + c) : 1 - a ≤ (1 - b) * (1 + c) := by
  rw [one_sub_mul, mul_one_add, sub_le_sub_iff, add_assoc, add_comm c]
  gcongr

