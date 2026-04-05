import Mathlib

variable {F : Type v'} {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B] [NonUnitalNonAssocSemiring C]

variable [Module R A] [Module R B] [Module R C]

variable {S : NonUnitalSubalgebra R A}

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B]

theorem map_mono {S₁ S₂ : NonUnitalSubalgebra R A} {f : F} :
    S₁ ≤ S₂ → (NonUnitalSubalgebra.map f S₁ : NonUnitalSubalgebra R B) ≤ NonUnitalSubalgebra.map f S₂ := Set.image_mono

