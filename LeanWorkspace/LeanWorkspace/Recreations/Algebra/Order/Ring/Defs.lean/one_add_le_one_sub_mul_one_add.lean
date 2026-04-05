import Mathlib

variable {R : Type u}

variable [Ring R] [PartialOrder R] [IsOrderedRing R] {a b c : R}

theorem one_add_le_one_sub_mul_one_add (h : a + b + b * c ≤ c) : 1 + a ≤ (1 - b) * (1 + c) := by
  rw [one_sub_mul, mul_one_add, le_sub_iff_add_le, add_assoc, ← add_assoc a]
  gcongr

