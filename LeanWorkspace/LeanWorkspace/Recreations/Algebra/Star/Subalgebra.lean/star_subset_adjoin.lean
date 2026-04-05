import Mathlib

variable {F R A B : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]

variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

theorem star_subset_adjoin (s : Set A) : star s ⊆ StarAlgebra.adjoin R s := Set.subset_union_right.trans Algebra.subset_adjoin

