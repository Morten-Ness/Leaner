import Mathlib

variable {F : Type v'} {R' : Type u'} {R : Type u}

variable {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [NonUnitalSemiring A] [StarRing A] [Module R A]

variable [NonUnitalSemiring B] [StarRing B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B]

variable (S : NonUnitalStarSubalgebra R A)

variable (S₁ : NonUnitalStarSubalgebra R B)

theorem coe_prod : (NonUnitalStarSubalgebra.prod S S₁ : Set (A × B)) = (S : Set A) ×ˢ S₁ := rfl

