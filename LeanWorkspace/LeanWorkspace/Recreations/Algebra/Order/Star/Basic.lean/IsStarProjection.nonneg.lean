import Mathlib

open scoped NNRat

variable {R A : Type*}

variable [NonUnitalSemiring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]

theorem IsStarProjection.nonneg {p : R} (hp : IsStarProjection p) : 0 ≤ p := hp.isIdempotentElem ▸ hp.isSelfAdjoint.mul_self_nonneg

