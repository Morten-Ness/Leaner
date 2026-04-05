import Mathlib

variable {F R A B C : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [StarRing A] [Algebra R A] [StarModule R A]

variable [Semiring B] [StarRing B] [Algebra R B] [StarModule R B]

variable [Semiring C] [StarRing C] [Algebra R C] [StarModule R C]

theorem toNonUnitalStarSubalgebra_injective : Function.Injective
    (StarSubalgebra.toNonUnitalStarSubalgebra : StarSubalgebra R A → NonUnitalStarSubalgebra R A) := fun _ _ ↦ by simp [SetLike.ext_iff]

