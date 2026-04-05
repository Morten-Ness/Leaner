import Mathlib

variable {F : Type v'} {R' : Type u'} {R : Type u}

variable {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [NonUnitalSemiring A] [StarRing A] [Module R A]

variable [NonUnitalSemiring B] [StarRing B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B]

variable (S : NonUnitalStarSubalgebra R A)

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem centralizer_univ : NonUnitalStarSubalgebra.centralizer R Set.univ = NonUnitalStarSubalgebra.center R A := SetLike.ext' <| by rw [NonUnitalStarSubalgebra.coe_centralizer, Set.univ_union, NonUnitalStarSubalgebra.coe_center, Set.centralizer_univ]

