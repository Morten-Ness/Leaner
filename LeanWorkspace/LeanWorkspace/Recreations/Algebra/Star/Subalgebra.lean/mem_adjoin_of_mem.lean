import Mathlib

variable {F R A B : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]

variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

theorem mem_adjoin_of_mem {s : Set A} {x : A} (hx : x ∈ s) : x ∈ StarAlgebra.adjoin R s := StarAlgebra.subset_adjoin R s hx

