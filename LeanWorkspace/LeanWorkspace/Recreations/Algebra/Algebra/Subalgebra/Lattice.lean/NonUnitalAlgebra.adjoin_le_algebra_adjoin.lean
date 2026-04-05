import Mathlib

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable (R) [CommSemiring R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]

theorem NonUnitalAlgebra.adjoin_le_algebra_adjoin (s : Set A) :
    Algebra.adjoin R s ≤ (Algebra.adjoin R s).toNonUnitalSubalgebra := Algebra.adjoin_le Algebra.subset_adjoin

