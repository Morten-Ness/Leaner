import Mathlib

open scoped NNRat

variable {R A : Type*}

variable [Semiring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]

theorem IsSelfAdjoint.sq_nonneg {a : R} (ha : IsSelfAdjoint a) : 0 ≤ a ^ 2 := by
  simp [sq, ha.mul_self_nonneg]

