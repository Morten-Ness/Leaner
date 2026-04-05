import Mathlib

variable {F : Type v'} {R' : Type u'} {R : Type u}

variable {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R] [StarRing R]

variable [NonUnitalSemiring A] [StarRing A] [Module R A]

variable [NonUnitalSemiring B] [StarRing B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B]

theorem map_top [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A] (f : F) :
    (⊤ : NonUnitalStarSubalgebra R A).map f = NonUnitalStarAlgHom.range f := SetLike.coe_injective Set.image_univ

