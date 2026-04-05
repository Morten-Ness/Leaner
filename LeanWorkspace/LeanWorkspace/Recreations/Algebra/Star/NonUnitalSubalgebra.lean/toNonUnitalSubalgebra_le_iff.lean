import Mathlib

variable {F : Type v'} {R' : Type u'} {R : Type u}

variable {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [NonUnitalNonAssocSemiring A] [Module R A] [Star A]

variable [NonUnitalNonAssocSemiring B] [Module R B] [Star B]

variable [NonUnitalNonAssocSemiring C] [Module R C] [Star C]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B]

theorem toNonUnitalSubalgebra_le_iff {S₁ S₂ : NonUnitalStarSubalgebra R A} :
    S₁.toNonUnitalSubalgebra ≤ S₂.toNonUnitalSubalgebra ↔ S₁ ≤ S₂ := Iff.rfl

