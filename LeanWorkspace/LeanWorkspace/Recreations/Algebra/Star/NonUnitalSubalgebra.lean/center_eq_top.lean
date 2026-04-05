import Mathlib

variable {F : Type v'} {R' : Type u'} {R : Type u}

variable {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [NonUnitalSemiring A] [StarRing A] [Module R A]

variable [NonUnitalSemiring B] [StarRing B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B]

variable (S : NonUnitalStarSubalgebra R A)

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem center_eq_top (A : Type*) [StarRing R] [NonUnitalCommSemiring A] [StarRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A] : NonUnitalStarSubalgebra.center R A = ⊤ := SetLike.coe_injective (Set.center_eq_univ A)

