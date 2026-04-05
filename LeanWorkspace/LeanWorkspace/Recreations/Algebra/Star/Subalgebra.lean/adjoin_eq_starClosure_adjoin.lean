import Mathlib

variable {F R A B : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]

variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

theorem adjoin_eq_starClosure_adjoin (s : Set A) : StarAlgebra.adjoin R s = (Algebra.adjoin R s).starClosure := StarSubalgebra.toSubalgebra_injective <|
    show Algebra.adjoin R (s ∪ star s) = Algebra.adjoin R s ⊔ star (Algebra.adjoin R s) from
      (Subalgebra.star_adjoin_comm R s).symm ▸ Algebra.adjoin_union s (star s)

