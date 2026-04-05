import Mathlib

variable {F : Type v'} {R' : Type u'} {R : Type u}

variable {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [NonUnitalSemiring A] [StarRing A] [Module R A]

variable [NonUnitalSemiring B] [StarRing B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B]

variable (S : NonUnitalStarSubalgebra R A)

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem centralizer_le (s t : Set A) (h : s ⊆ t) : NonUnitalStarSubalgebra.centralizer R t ≤ NonUnitalStarSubalgebra.centralizer R s := Set.centralizer_subset (Set.union_subset_union h <| Set.preimage_mono h)

