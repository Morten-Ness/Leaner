import Mathlib

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable (R) [CommSemiring R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]

theorem Algebra.adjoin_nonUnitalSubalgebra (s : Set A) :
    Algebra.adjoin R (NonUnitalAlgebra.adjoin R s : Set A) = Algebra.adjoin R s := le_antisymm
    (Algebra.adjoin_le <| NonUnitalAlgebra.adjoin_le_algebra_adjoin R s)
    (Algebra.adjoin_le <| (NonUnitalAlgebra.subset_adjoin R).trans Algebra.subset_adjoin)

