import Mathlib

variable {F R A B : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]

variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

theorem adjoin_le_iff {S : StarSubalgebra R A} {s : Set A} : StarAlgebra.adjoin R s ≤ S ↔ s ⊆ S := StarAlgebra.gc _ _

