import Mathlib

open scoped NNRat

variable {R A : Type*}

variable [NonUnitalSemiring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]

theorem IsSelfAdjoint.mul_self_nonneg {a : R} (ha : IsSelfAdjoint a) : 0 ≤ a * a := by
  simpa [ha.star_eq] using star_mul_self_nonneg a

