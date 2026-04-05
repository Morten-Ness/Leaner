import Mathlib

variable {F : Type v'} {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B] [NonUnitalNonAssocSemiring C]

variable [Module R A] [Module R B] [Module R C]

variable {S : NonUnitalSubalgebra R A}

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B]

theorem gc_map_comap (f : F) :
    GaloisConnection (NonUnitalSubalgebra.map f : NonUnitalSubalgebra R A → NonUnitalSubalgebra R B) (NonUnitalSubalgebra.comap f) := fun _ _ => NonUnitalSubalgebra.map_le

