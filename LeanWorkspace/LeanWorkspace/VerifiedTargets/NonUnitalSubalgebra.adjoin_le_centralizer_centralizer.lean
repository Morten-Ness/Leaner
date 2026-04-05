import Mathlib

variable {R A : Type*} [CommSemiring R] [NonUnitalSemiring A]

variable [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]

theorem adjoin_le_centralizer_centralizer (s : Set A) :
    NonUnitalAlgebra.adjoin R s ≤ NonUnitalSubalgebra.centralizer R (NonUnitalSubalgebra.centralizer R s) := NonUnitalAlgebra.adjoin_le Set.subset_centralizer_centralizer

