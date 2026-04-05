import Mathlib

open scoped NNRat

variable {R A : Type*}

variable [NonUnitalSemiring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]

theorem mul_star_self_pos [Nontrivial R] {x : R} (hx : IsRegular x) : 0 < x * star x := by
  simpa using star_mul_self_pos hx.star

