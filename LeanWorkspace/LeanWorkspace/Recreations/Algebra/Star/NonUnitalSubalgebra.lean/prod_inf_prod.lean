import Mathlib

variable {F : Type v'} {R' : Type u'} {R : Type u}

variable {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [NonUnitalSemiring A] [StarRing A] [Module R A]

variable [NonUnitalSemiring B] [StarRing B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B]

variable (S : NonUnitalStarSubalgebra R A)

variable (S₁ : NonUnitalStarSubalgebra R B)

variable [StarRing R]

variable [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]

variable [IsScalarTower R B B] [SMulCommClass R B B] [StarModule R B]

theorem prod_inf_prod {S T : NonUnitalStarSubalgebra R A} {S₁ T₁ : NonUnitalStarSubalgebra R B} :
    S.prod S₁ ⊓ T.prod T₁ = (S ⊓ T).prod (S₁ ⊓ T₁) := SetLike.coe_injective Set.prod_inter_prod

