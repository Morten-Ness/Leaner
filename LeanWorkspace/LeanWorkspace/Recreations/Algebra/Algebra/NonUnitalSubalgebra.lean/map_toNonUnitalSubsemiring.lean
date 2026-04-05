import Mathlib

variable {F : Type v'} {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B] [NonUnitalNonAssocSemiring C]

variable [Module R A] [Module R B] [Module R C]

variable {S : NonUnitalSubalgebra R A}

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B]

theorem map_toNonUnitalSubsemiring {S : NonUnitalSubalgebra R A} {f : F} :
    (NonUnitalSubalgebra.map f S).toNonUnitalSubsemiring = S.toNonUnitalSubsemiring.map (f : A →ₙ+* B) := SetLike.coe_injective rfl

