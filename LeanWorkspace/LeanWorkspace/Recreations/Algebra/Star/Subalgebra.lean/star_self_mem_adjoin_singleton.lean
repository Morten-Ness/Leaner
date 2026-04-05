import Mathlib

variable {F R A B : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]

variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

theorem star_self_mem_adjoin_singleton (x : A) : star x ∈ StarAlgebra.adjoin R ({x} : Set A) := star_mem <| StarAlgebra.self_mem_adjoin_singleton R x

