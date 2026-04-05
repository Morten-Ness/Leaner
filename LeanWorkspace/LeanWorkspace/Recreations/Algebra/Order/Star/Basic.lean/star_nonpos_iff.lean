import Mathlib

open scoped NNRat

variable {R A : Type*}

variable [NonUnitalSemiring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]

theorem star_nonpos_iff {x : R} : star x ≤ 0 ↔ x ≤ 0 := by
  simpa using star_le_star_iff (x := x) (y := 0)

