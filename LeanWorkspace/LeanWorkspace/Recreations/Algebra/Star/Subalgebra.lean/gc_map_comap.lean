import Mathlib

variable {F R A B C : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [StarRing A] [Algebra R A] [StarModule R A]

variable [Semiring B] [StarRing B] [Algebra R B] [StarModule R B]

variable [Semiring C] [StarRing C] [Algebra R C] [StarModule R C]

variable (S : StarSubalgebra R A)

theorem gc_map_comap (f : A →⋆ₐ[R] B) : GaloisConnection (StarSubalgebra.map f) (StarSubalgebra.comap f) := fun _S _U =>
  StarSubalgebra.map_le_iff_le_comap

