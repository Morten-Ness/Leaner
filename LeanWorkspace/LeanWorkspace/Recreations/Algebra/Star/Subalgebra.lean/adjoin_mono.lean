import Mathlib

variable {F R A B : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]

variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

theorem adjoin_mono {s t : Set A} (H : s ⊆ t) : StarAlgebra.adjoin R s ≤ StarAlgebra.adjoin R t := StarAlgebra.gc.monotone_l H

