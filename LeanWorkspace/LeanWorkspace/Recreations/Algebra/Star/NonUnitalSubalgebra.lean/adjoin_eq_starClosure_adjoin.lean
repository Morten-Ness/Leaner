import Mathlib

open scoped Pointwise

variable {F : Type v'} {R' : Type u'} {R : Type u}

variable {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R] [StarRing R]

variable [NonUnitalSemiring A] [StarRing A] [Module R A]

variable [NonUnitalSemiring B] [StarRing B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B]

variable [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]

theorem adjoin_eq_starClosure_adjoin (s : Set A) :
    NonUnitalStarAlgebra.adjoin R s = (NonUnitalAlgebra.adjoin R s).starClosure := NonUnitalStarSubalgebra.toNonUnitalSubalgebra_injective <| show
    NonUnitalAlgebra.adjoin R (s ∪ star s) =
      NonUnitalAlgebra.adjoin R s ⊔ star (NonUnitalAlgebra.adjoin R s)
    from
      (NonUnitalSubalgebra.star_adjoin_comm R s).symm ▸ NonUnitalAlgebra.adjoin_union s (star s)

