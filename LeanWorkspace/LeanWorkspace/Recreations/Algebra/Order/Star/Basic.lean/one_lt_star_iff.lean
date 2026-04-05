import Mathlib

open scoped NNRat

variable {R A : Type*}

variable [Semiring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]

theorem one_lt_star_iff {x : R} : 1 < star x ↔ 1 < x := by
  simpa using star_lt_star_iff (x := 1) (y := x)

