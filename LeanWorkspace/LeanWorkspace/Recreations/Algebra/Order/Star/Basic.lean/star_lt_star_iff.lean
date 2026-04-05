import Mathlib

open scoped NNRat

variable {R A : Type*}

variable [NonUnitalSemiring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]

theorem star_lt_star_iff {x y : R} : star x < star y ↔ x < y := by
  by_cases h : x = y
  · simp [h]
  · simpa [le_iff_lt_or_eq, h] using star_le_star_iff (x := x) (y := y)

