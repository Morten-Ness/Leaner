import Mathlib

variable {R A : Type*} [CommSemiring R] [StarRing R] [Semiring A] [StarRing A] [Algebra R A]
  [StarModule R A]

theorem StarAlgebra.adjoin_nonUnitalStarSubalgebra (s : Set A) :
    StarAlgebra.adjoin R (NonUnitalStarAlgebra.adjoin R s : Set A) = StarAlgebra.adjoin R s := le_antisymm
    (StarAlgebra.adjoin_le <| NonUnitalStarAlgebra.adjoin_le_starAlgebra_adjoin R s)
    (StarAlgebra.adjoin_le <| (NonUnitalStarAlgebra.subset_adjoin R s).trans <| StarAlgebra.subset_adjoin R _)

