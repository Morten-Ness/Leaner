import Mathlib

open scoped NNRat

variable {R A : Type*}

variable [Semiring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]

theorem star_lt_one_iff {x : R} : star x < 1 ↔ x < 1 := by
  simpa using star_lt_star_iff (x := x) (y := 1)

