import Mathlib

open scoped NNRat

variable {R A : Type*}

variable [Semiring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]

theorem star_le_one_iff {x : R} : star x ≤ 1 ↔ x ≤ 1 := by
  simpa using star_le_star_iff (x := x) (y := 1)

