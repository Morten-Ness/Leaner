import Mathlib

open scoped NNRat

variable {R A : Type*}

variable [Ring R] [PartialOrder R] [StarRing R] [StarOrderedRing R] {p : R}

theorem le_one (hp : IsStarProjection p) : p ≤ 1 := sub_nonneg.mp IsStarProjection.one_sub_nonneg hp

