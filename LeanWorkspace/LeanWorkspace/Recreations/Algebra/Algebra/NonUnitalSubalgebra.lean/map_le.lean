import Mathlib

variable {F : Type v'} {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B] [NonUnitalNonAssocSemiring C]

variable [Module R A] [Module R B] [Module R C]

variable {S : NonUnitalSubalgebra R A}

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B]

theorem map_le {S : NonUnitalSubalgebra R A} {f : F} {U : NonUnitalSubalgebra R B} :
    NonUnitalSubalgebra.map f S ≤ U ↔ S ≤ NonUnitalSubalgebra.comap f U := Set.image_subset_iff

