import Mathlib

open scoped NNRat

variable {R A : Type*}

variable [NonUnitalSemiring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]

theorem star_right_conjugate_le_conjugate {a b : R} (hab : a ≤ b) (c : R) :
    c * a * star c ≤ c * b * star c := by
  simpa only [star_star] using star_left_conjugate_le_conjugate hab (star c)

