import Mathlib

variable {F R A B C : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [StarRing A] [Algebra R A] [StarModule R A]

variable [Semiring B] [StarRing B] [Algebra R B] [StarModule R B]

variable [Semiring C] [StarRing C] [Algebra R C] [StarModule R C]

variable (S : StarSubalgebra R A)

theorem centralizer_le (s t : Set A) (h : s ⊆ t) : StarSubalgebra.centralizer R t ≤ StarSubalgebra.centralizer R s := Set.centralizer_subset (Set.union_subset_union h <| Set.preimage_mono h)

