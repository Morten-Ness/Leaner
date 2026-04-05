import Mathlib

variable {R A : Type*} [CommSemiring R] [StarRing R] [Semiring A] [StarRing A] [Algebra R A]
  [StarModule R A]

theorem NonUnitalStarAlgebra.adjoin_le_starAlgebra_adjoin (s : Set A) :
    StarAlgebra.adjoin R s ≤ (StarAlgebra.adjoin R s).toNonUnitalStarSubalgebra := StarAlgebra.adjoin_le <| StarAlgebra.subset_adjoin R s

