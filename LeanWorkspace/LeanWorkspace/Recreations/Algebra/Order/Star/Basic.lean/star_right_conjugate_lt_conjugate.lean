import Mathlib

open scoped NNRat

variable {R A : Type*}

variable [NonUnitalSemiring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]

theorem star_right_conjugate_lt_conjugate {a b : R} (hab : a < b) {c : R} (hc : IsRegular c) :
    c * a * star c < c * b * star c := by
  simpa only [star_star] using star_left_conjugate_lt_conjugate hab hc.star

