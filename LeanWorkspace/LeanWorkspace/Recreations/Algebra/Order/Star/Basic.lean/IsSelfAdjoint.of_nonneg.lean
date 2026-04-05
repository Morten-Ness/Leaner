import Mathlib

open scoped NNRat

variable {R A : Type*}

variable [NonUnitalSemiring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]

theorem IsSelfAdjoint.of_nonneg {x : R} (hx : 0 ≤ x) : IsSelfAdjoint x := .mono hx <| .zero R

