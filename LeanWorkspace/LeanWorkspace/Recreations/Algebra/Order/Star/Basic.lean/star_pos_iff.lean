import Mathlib

open scoped NNRat

variable {R A : Type*}

variable [NonUnitalSemiring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]

theorem star_pos_iff {x : R} : 0 < star x ↔ 0 < x := by
  simpa using star_lt_star_iff (x := 0) (y := x)

