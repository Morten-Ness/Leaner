import Mathlib

variable {F R A B : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A]

variable [Semiring B] [Algebra R B] [StarRing B]

variable [StarModule R A]

variable [FunLike F A B] [AlgHomClass F R A B] [StarHomClass F A B] (f g : F)

variable [StarModule R B]

theorem map_adjoin (f : A →⋆ₐ[R] B) (s : Set A) :
    StarSubalgebra.map f (StarAlgebra.adjoin R s) = StarAlgebra.adjoin R (f '' s) := GaloisConnection.l_comm_of_u_comm Set.image_preimage (StarSubalgebra.gc_map_comap f) StarAlgebra.gc
    StarAlgebra.gc fun _ => rfl

