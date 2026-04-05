import Mathlib

variable {F R A B C : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [StarRing A] [Algebra R A] [StarModule R A]

variable [Semiring B] [StarRing B] [Algebra R B] [StarModule R B]

variable [Semiring C] [StarRing C] [Algebra R C] [StarModule R C]

variable (S : StarSubalgebra R A)

theorem map_le_iff_le_comap {S : StarSubalgebra R A} {f : A →⋆ₐ[R] B} {U : StarSubalgebra R B} :
    StarSubalgebra.map f S ≤ U ↔ S ≤ StarSubalgebra.comap f U := Set.image_subset_iff

