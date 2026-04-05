import Mathlib

variable {F R A B : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]

variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

theorem coe_sInf (S : Set (StarSubalgebra R A)) : (↑(sInf S) : Set A) = ⋂ s ∈ S, ↑s := sInf_image

