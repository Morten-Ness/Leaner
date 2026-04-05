import Mathlib

open scoped Pointwise

variable {F : Type v'} {R' : Type u'} {R : Type u}

variable {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R] [StarRing R]

variable [NonUnitalSemiring A] [StarRing A] [Module R A]

variable [NonUnitalSemiring B] [StarRing B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B]

variable [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]

theorem map_inf [IsScalarTower R B B] [SMulCommClass R B B] [StarModule R B] (f : F)
    (hf : Function.Injective f) (S T : NonUnitalStarSubalgebra R A) :
    ((S ⊓ T).map f : NonUnitalStarSubalgebra R B) = S.map f ⊓ T.map f := SetLike.coe_injective (Set.image_inter hf)

