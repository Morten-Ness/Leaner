import Mathlib

variable {F R A B : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]

variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

theorem subset_adjoin (s : Set A) : s ⊆ StarAlgebra.adjoin R s := Set.subset_union_left.trans Algebra.subset_adjoin

