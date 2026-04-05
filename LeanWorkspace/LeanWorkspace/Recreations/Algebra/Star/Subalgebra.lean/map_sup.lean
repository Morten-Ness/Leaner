import Mathlib

variable {F R A B : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]

variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

theorem map_sup (f : A →⋆ₐ[R] B) (S T : StarSubalgebra R A) : StarSubalgebra.map f (S ⊔ T) = StarSubalgebra.map f S ⊔ StarSubalgebra.map f T := (StarSubalgebra.gc_map_comap f).l_sup

