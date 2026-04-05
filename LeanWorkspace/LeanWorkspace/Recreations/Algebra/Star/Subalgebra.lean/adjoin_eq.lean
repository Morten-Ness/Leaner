import Mathlib

variable {F R A B : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]

variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

theorem adjoin_eq (S : StarSubalgebra R A) : StarAlgebra.adjoin R (S : Set A) = S := le_antisymm (StarAlgebra.adjoin_le le_rfl) (StarAlgebra.subset_adjoin R (S : Set A))

