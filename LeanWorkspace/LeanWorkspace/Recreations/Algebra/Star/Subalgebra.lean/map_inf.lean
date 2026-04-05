import Mathlib

variable {F R A B : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]

variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

theorem map_inf (f : A →⋆ₐ[R] B) (hf : Function.Injective f) (S T : StarSubalgebra R A) :
    StarSubalgebra.map f (S ⊓ T) = StarSubalgebra.map f S ⊓ StarSubalgebra.map f T := SetLike.coe_injective (Set.image_inter hf)

