import Mathlib

open scoped Pointwise

variable {F : Type v'} {R' : Type u'} {R : Type u}

variable {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R] [StarRing R]

variable [NonUnitalSemiring A] [StarRing A] [Module R A]

variable [NonUnitalSemiring B] [StarRing B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B]

variable [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]

theorem _root_.NonUnitalSubalgebra.starClosure_eq_adjoin (S : NonUnitalSubalgebra R A) :
    S.starClosure = NonUnitalStarAlgebra.adjoin R (S : Set A) := le_antisymm (NonUnitalSubalgebra.starClosure_le_iff.2 <| NonUnitalStarAlgebra.subset_adjoin R (S : Set A))
    (NonUnitalStarAlgebra.adjoin_le (le_sup_left : S ≤ S ⊔ star S))

