import Mathlib

variable {F : Type v'} {R' : Type u'} {R : Type u}

variable {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [NonUnitalSemiring A] [StarRing A] [Module R A]

variable [NonUnitalSemiring B] [StarRing B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B]

variable (S : NonUnitalStarSubalgebra R A)

theorem inclusion_self {S : NonUnitalStarSubalgebra R A} :
    NonUnitalStarSubalgebra.inclusion (le_refl S) = NonUnitalAlgHom.id R S := NonUnitalAlgHom.ext fun _x => Subtype.ext rfl

