import Mathlib

variable {F : Type v'} {R' : Type u'} {R : Type u}

variable {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [NonUnitalSemiring A] [StarRing A] [Module R A]

variable [NonUnitalSemiring B] [StarRing B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B]

variable (S : NonUnitalStarSubalgebra R A)

variable (S₁ : NonUnitalStarSubalgebra R B)

theorem prod_mono {S T : NonUnitalStarSubalgebra R A} {S₁ T₁ : NonUnitalStarSubalgebra R B} :
    S ≤ T → S₁ ≤ T₁ → NonUnitalStarSubalgebra.prod S S₁ ≤ NonUnitalStarSubalgebra.prod T T₁ := Set.prod_mono

