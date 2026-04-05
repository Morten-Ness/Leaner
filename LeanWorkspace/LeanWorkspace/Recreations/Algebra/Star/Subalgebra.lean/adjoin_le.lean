import Mathlib

variable {F R A B : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]

variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

theorem adjoin_le {S : StarSubalgebra R A} {s : Set A} (hs : s ⊆ S) : StarAlgebra.adjoin R s ≤ S := StarAlgebra.gc.l_le hs

