import Mathlib

open scoped NNRat

variable {R A : Type*}

variable [NonUnitalSemiring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]

theorem star_le_iff {x y : R} : star x ≤ y ↔ x ≤ star y := by rw [← star_le_star_iff, star_star]

