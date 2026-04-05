import Mathlib

variable {F : Type*} (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

variable [NonUnitalNonAssocSemiring B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B]

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem map_inf [IsScalarTower R B B] [SMulCommClass R B B]
    (f : F) (hf : Function.Injective f) (S T : NonUnitalSubalgebra R A) :
    ((S ⊓ T).map f : NonUnitalSubalgebra R B) = S.map f ⊓ T.map f := SetLike.coe_injective (Set.image_inter hf)

