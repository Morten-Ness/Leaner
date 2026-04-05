import Mathlib

variable {F R A B C : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [StarRing A] [Algebra R A] [StarModule R A]

variable [Semiring B] [StarRing B] [Algebra R B] [StarModule R B]

variable [Semiring C] [StarRing C] [Algebra R C] [StarModule R C]

theorem toNonUnitalStarSubalgebra_inj {S U : StarSubalgebra R A} :
    S.toNonUnitalStarSubalgebra = U.toNonUnitalStarSubalgebra ↔ S = U := StarSubalgebra.toNonUnitalStarSubalgebra_injective.eq_iff

