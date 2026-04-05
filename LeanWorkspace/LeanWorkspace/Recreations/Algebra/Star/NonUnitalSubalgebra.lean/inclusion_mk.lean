import Mathlib

variable {F : Type v'} {R' : Type u'} {R : Type u}

variable {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [NonUnitalSemiring A] [StarRing A] [Module R A]

variable [NonUnitalSemiring B] [StarRing B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B]

variable (S : NonUnitalStarSubalgebra R A)

theorem inclusion_mk {S T : NonUnitalStarSubalgebra R A} (h : S ≤ T) (x : A) (hx : x ∈ S) :
    NonUnitalStarSubalgebra.inclusion h ⟨x, hx⟩ = ⟨x, h hx⟩ := rfl

