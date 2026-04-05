import Mathlib

variable {F : Type v'} {R' : Type u'} {R : Type u}

variable {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [NonUnitalNonAssocSemiring A] [Module R A] [Star A]

variable [NonUnitalNonAssocSemiring B] [Module R B] [Star B]

variable [NonUnitalNonAssocSemiring C] [Module R C] [Star C]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B]

variable (S : NonUnitalStarSubalgebra R A)

theorem map_injective {f : F} (hf : Function.Injective f) :
    Function.Injective (NonUnitalStarSubalgebra.map f : NonUnitalStarSubalgebra R A → NonUnitalStarSubalgebra R B) := fun _S₁ _S₂ ih =>
  NonUnitalStarSubalgebra.ext <| Set.ext_iff.1 <| Set.image_injective.2 hf <| Set.ext <| SetLike.ext_iff.mp ih

