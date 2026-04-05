import Mathlib

variable {F : Type v'} {R' : Type u'} {R : Type u}

variable {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [NonUnitalNonAssocSemiring A] [Module R A] [Star A]

variable [NonUnitalNonAssocSemiring B] [Module R B] [Star B]

variable [NonUnitalNonAssocSemiring C] [Module R C] [Star C]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B]

variable (S : NonUnitalStarSubalgebra R A)

theorem map_le {S : NonUnitalStarSubalgebra R A} {f : F} {U : NonUnitalStarSubalgebra R B} :
    NonUnitalStarSubalgebra.map f S ≤ U ↔ S ≤ NonUnitalStarSubalgebra.comap f U := Set.image_subset_iff

