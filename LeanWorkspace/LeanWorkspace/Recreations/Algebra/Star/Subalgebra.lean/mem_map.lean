import Mathlib

variable {F R A B C : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [StarRing A] [Algebra R A] [StarModule R A]

variable [Semiring B] [StarRing B] [Algebra R B] [StarModule R B]

variable [Semiring C] [StarRing C] [Algebra R C] [StarModule R C]

variable (S : StarSubalgebra R A)

theorem mem_map {S : StarSubalgebra R A} {f : A →⋆ₐ[R] B} {y : B} :
    y ∈ StarSubalgebra.map f S ↔ ∃ x ∈ S, f x = y := Subsemiring.mem_map

