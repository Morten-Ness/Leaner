import Mathlib

open scoped NNRat

variable {R A : Type*}

variable [Ring R] [PartialOrder R] [StarRing R] [StarOrderedRing R] {p : R}

theorem one_sub_nonneg (hp : IsStarProjection p) : 0 ≤ 1 - p := hp.one_sub.nonneg

