import Mathlib

variable {F R A B : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]

variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

theorem sInf_toSubalgebra (S : Set (StarSubalgebra R A)) :
    (sInf S).toSubalgebra = sInf (StarSubalgebra.toSubalgebra '' S) := SetLike.coe_injective <| by simp

