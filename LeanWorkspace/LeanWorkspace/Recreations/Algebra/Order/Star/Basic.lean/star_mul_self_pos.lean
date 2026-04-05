import Mathlib

open scoped NNRat

variable {R A : Type*}

variable [NonUnitalSemiring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]

theorem star_mul_self_pos [Nontrivial R] {x : R} (hx : IsRegular x) : 0 < star x * x := by
  rw [(star_mul_self_nonneg _).lt_iff_ne, ← mul_zero (star x), hx.star.left.ne_iff]
  exact hx.ne_zero.symm

