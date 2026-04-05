import Mathlib

variable {F : Type v'} {R' : Type u'} {R : Type u}

variable {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [NonUnitalNonAssocSemiring A] [Module R A] [Star A]

variable [NonUnitalNonAssocSemiring B] [Module R B] [Star B]

variable [NonUnitalNonAssocSemiring C] [Module R C] [Star C]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B]

theorem toNonUnitalSubalgebra_injective :
    Function.Injective
      (toNonUnitalSubalgebra : NonUnitalStarSubalgebra R A → NonUnitalSubalgebra R A) := fun S T h =>
  NonUnitalStarSubalgebra.ext fun x => by rw [← NonUnitalStarSubalgebra.mem_toNonUnitalSubalgebra, ← NonUnitalStarSubalgebra.mem_toNonUnitalSubalgebra, h]

