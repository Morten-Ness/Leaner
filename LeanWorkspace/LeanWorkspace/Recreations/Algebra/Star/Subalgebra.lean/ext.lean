import Mathlib

variable {F R A B C : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [StarRing A] [Algebra R A] [StarModule R A]

variable [Semiring B] [StarRing B] [Algebra R B] [StarModule R B]

variable [Semiring C] [StarRing C] [Algebra R C] [StarModule R C]

theorem ext {S T : StarSubalgebra R A} (h : ∀ x : A, x ∈ S ↔ x ∈ T) : S = T := SetLike.ext h

