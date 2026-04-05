import Mathlib

variable {F R A B : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]

variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

theorem self_mem_adjoin_singleton (x : A) : x ∈ StarAlgebra.adjoin R ({x} : Set A) := Algebra.subset_adjoin <| Set.mem_union_left _ (Set.mem_singleton x)

