import Mathlib

open scoped NNRat

variable {R A : Type*}

variable [NonUnitalSemiring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]

theorem conjugate_le_conjugate_of_nonneg {a b : R} (hab : a ≤ b) {c : R} (hc : 0 ≤ c) :
    c * a * c ≤ c * b * c := IsSelfAdjoint.of_nonneg hc |>.conjugate_le_conjugate hab

