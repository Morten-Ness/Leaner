import Mathlib

variable {F : Type*} (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

variable [NonUnitalNonAssocSemiring B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B]

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem toNonUnitalSubring_top {R A : Type*} [CommRing R] [NonUnitalNonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] :
    (⊤ : NonUnitalSubalgebra R A).toNonUnitalSubring = ⊤ := rfl

