import Mathlib

open scoped NNRat

variable {R A : Type*}

variable [Semiring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]

theorem one_le_star_iff {x : R} : 1 ≤ star x ↔ 1 ≤ x := by
  simpa using star_le_star_iff (x := 1) (y := x)

