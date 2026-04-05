import Mathlib

open scoped NNRat

variable {R A : Type*}

variable [NonUnitalSemiring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]

theorem star_right_conjugate_pos {a : R} (ha : 0 < a) {c : R} (hc : IsRegular c) :
    0 < c * a * star c := by
  simpa only [star_star] using star_left_conjugate_pos ha hc.star

