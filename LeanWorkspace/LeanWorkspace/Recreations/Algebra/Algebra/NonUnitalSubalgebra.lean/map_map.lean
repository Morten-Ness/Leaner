import Mathlib

variable {F : Type v'} {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B] [NonUnitalNonAssocSemiring C]

variable [Module R A] [Module R B] [Module R C]

variable {S : NonUnitalSubalgebra R A}

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B]

theorem map_map (S : NonUnitalSubalgebra R A) (g : B →ₙₐ[R] C) (f : A →ₙₐ[R] B) :
    (S.map f).map g = S.map (g.comp f) := SetLike.coe_injective <| Set.image_image _ _ _

