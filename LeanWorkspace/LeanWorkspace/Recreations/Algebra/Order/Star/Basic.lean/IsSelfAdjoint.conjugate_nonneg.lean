import Mathlib

open scoped NNRat

variable {R A : Type*}

variable [NonUnitalSemiring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]

theorem IsSelfAdjoint.conjugate_nonneg {a : R} (ha : 0 ≤ a) {c : R}
    (hc : IsSelfAdjoint c) : 0 ≤ c * a * c := by
  nth_rewrite 2 [← hc]; exact star_right_conjugate_nonneg ha c

