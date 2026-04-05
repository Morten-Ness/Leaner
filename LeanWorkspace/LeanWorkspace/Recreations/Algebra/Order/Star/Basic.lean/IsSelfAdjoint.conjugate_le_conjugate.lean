import Mathlib

open scoped NNRat

variable {R A : Type*}

variable [NonUnitalSemiring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]

theorem IsSelfAdjoint.conjugate_le_conjugate {a b : R} (hab : a ≤ b) {c : R}
    (hc : IsSelfAdjoint c) : c * a * c ≤ c * b * c := by
  simpa only [hc.star_eq] using star_left_conjugate_le_conjugate hab c

