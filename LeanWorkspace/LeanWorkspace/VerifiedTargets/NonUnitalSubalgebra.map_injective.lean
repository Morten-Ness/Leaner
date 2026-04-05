import Mathlib

variable {F : Type v'} {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B] [NonUnitalNonAssocSemiring C]

variable [Module R A] [Module R B] [Module R C]

variable {S : NonUnitalSubalgebra R A}

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B]

theorem map_injective {f : F} (hf : Function.Injective f) :
    Function.Injective (NonUnitalSubalgebra.map f : NonUnitalSubalgebra R A → NonUnitalSubalgebra R B) := fun _S₁ _S₂ ih =>
  NonUnitalSubalgebra.ext <| Set.ext_iff.1 <| Set.image_injective.2 hf <| Set.ext <| SetLike.ext_iff.mp ih

