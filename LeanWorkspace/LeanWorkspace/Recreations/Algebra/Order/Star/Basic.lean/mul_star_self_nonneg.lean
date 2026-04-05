import Mathlib

open scoped NNRat

variable {R A : Type*}

variable [NonUnitalSemiring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]

theorem mul_star_self_nonneg (r : R) : 0 ≤ r * star r := by
  simpa only [star_star] using star_mul_self_nonneg (star r)

