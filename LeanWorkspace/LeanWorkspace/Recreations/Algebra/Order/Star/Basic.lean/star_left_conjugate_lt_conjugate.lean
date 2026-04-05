import Mathlib

open scoped NNRat

variable {R A : Type*}

variable [NonUnitalSemiring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]

theorem star_left_conjugate_lt_conjugate {a b : R} (hab : a < b) {c : R} (hc : IsRegular c) :
    star c * a * c < star c * b * c := by
  rw [(star_left_conjugate_le_conjugate hab.le _).lt_iff_ne, hc.right.ne_iff, hc.star.left.ne_iff]
  exact hab.ne

