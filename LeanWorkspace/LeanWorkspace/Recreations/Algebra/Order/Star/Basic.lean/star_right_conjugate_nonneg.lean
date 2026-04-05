import Mathlib

open scoped NNRat

variable {R A : Type*}

variable [NonUnitalSemiring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]

theorem star_right_conjugate_nonneg {a : R} (ha : 0 ≤ a) (c : R) : 0 ≤ c * a * star c := by
  simpa only [star_star] using star_left_conjugate_nonneg ha (star c)

