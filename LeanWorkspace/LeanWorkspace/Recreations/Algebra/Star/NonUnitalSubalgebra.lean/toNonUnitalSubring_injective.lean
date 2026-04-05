import Mathlib

variable {F : Type v'} {R' : Type u'} {R : Type u}

variable {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [NonUnitalNonAssocSemiring A] [Module R A] [Star A]

variable [NonUnitalNonAssocSemiring B] [Module R B] [Star B]

variable [NonUnitalNonAssocSemiring C] [Module R C] [Star C]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B]

variable (S : NonUnitalStarSubalgebra R A)

theorem toNonUnitalSubring_injective {R : Type u} {A : Type v} [CommRing R] [NonUnitalRing A]
    [Module R A] [Star A] :
    Function.Injective (NonUnitalStarSubalgebra.toNonUnitalSubring : NonUnitalStarSubalgebra R A → NonUnitalSubring A) := fun S T h => NonUnitalStarSubalgebra.ext fun x => by rw [← NonUnitalStarSubalgebra.mem_toNonUnitalSubring, ← NonUnitalStarSubalgebra.mem_toNonUnitalSubring, h]

