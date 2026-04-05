import Mathlib

variable {F R A B C : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [StarRing A] [Algebra R A] [StarModule R A]

variable [Semiring B] [StarRing B] [Algebra R B] [StarModule R B]

variable [Semiring C] [StarRing C] [Algebra R C] [StarModule R C]

theorem one_mem_toNonUnitalStarSubalgebra (S : StarSubalgebra R A) :
    1 ∈ S.toNonUnitalStarSubalgebra := S.one_mem'

