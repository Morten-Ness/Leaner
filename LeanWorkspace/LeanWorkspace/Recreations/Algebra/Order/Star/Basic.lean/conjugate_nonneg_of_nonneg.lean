import Mathlib

open scoped NNRat

variable {R A : Type*}

variable [NonUnitalSemiring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]

theorem conjugate_nonneg_of_nonneg {a : R} (ha : 0 ≤ a) {c : R} (hc : 0 ≤ c) :
    0 ≤ c * a * c := IsSelfAdjoint.of_nonneg hc |>.conjugate_nonneg ha

