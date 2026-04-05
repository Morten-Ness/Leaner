import Mathlib

open scoped NNRat

variable {R A : Type*}

variable [NonUnitalSemiring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]

theorem star_left_conjugate_pos {a : R} (ha : 0 < a) {c : R} (hc : IsRegular c) :
    0 < star c * a * c := by
  simpa only [mul_zero, zero_mul] using star_left_conjugate_lt_conjugate ha hc

