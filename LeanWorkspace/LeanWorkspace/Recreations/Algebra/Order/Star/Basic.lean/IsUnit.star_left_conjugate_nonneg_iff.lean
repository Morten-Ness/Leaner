import Mathlib

open scoped NNRat

variable {R A : Type*}

variable [Semiring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]

theorem IsUnit.star_left_conjugate_nonneg_iff {u x : R} (hu : IsUnit u) :
    0 ≤ star u * x * u ↔ 0 ≤ x := by
  simpa using hu.star.star_right_conjugate_nonneg_iff

