import Mathlib

variable {α M R : Type*}

variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R] {a : R}

theorem sq_pos_of_neg (ha : a < 0) : 0 < a ^ 2 := by rw [sq]; exact mul_pos_of_neg_of_neg ha ha

