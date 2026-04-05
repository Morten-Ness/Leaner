import Mathlib

variable {F : Type v'} {R' : Type u'} {R : Type u}

variable {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [NonUnitalNonAssocSemiring A] [Module R A] [Star A]

variable [NonUnitalNonAssocSemiring B] [Module R B] [Star B]

variable [NonUnitalNonAssocSemiring C] [Module R C] [Star C]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B]

theorem range_comp_le_range (f : A →⋆ₙₐ[R] B) (g : B →⋆ₙₐ[R] C) :
    NonUnitalStarAlgHom.range (g.comp f) ≤ NonUnitalStarAlgHom.range g := SetLike.coe_mono (Set.range_comp_subset_range f g)

