import Mathlib

open scoped Pointwise

variable {F : Type v'} {R' : Type u'} {R : Type u}

variable {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R] [StarRing R]

variable [NonUnitalSemiring A] [StarRing A] [Module R A]

variable [StarModule R A]

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem star_adjoin_comm (s : Set A) :
    star (NonUnitalAlgebra.adjoin R s) = NonUnitalAlgebra.adjoin R (star s) := have this :
    ∀ t : Set A, NonUnitalAlgebra.adjoin R (star t) ≤ star (NonUnitalAlgebra.adjoin R t) := fun _ =>
    NonUnitalAlgebra.adjoin_le fun _ hx => NonUnitalAlgebra.subset_adjoin R hx
  le_antisymm (by simpa only [star_star] using NonUnitalSubalgebra.star_mono (this (star s)))
    (this s)

