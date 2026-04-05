import Mathlib

variable {F : Type v'} {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B] [NonUnitalNonAssocSemiring C]

variable [Module R A] [Module R B] [Module R C]

variable {S : NonUnitalSubalgebra R A}

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B]

theorem map_toSubmodule {S : NonUnitalSubalgebra R A} {f : F} :
    -- TODO: introduce a better coercion from `NonUnitalAlgHomClass` to `LinearMap`
    (NonUnitalSubalgebra.map f S).toSubmodule = Submodule.map (LinearMapClass.linearMap f) S.toSubmodule := SetLike.coe_injective rfl

