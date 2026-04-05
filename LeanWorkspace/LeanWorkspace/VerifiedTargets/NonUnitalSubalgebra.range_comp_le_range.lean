import Mathlib

variable {F : Type v'} {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [NonUnitalNonAssocSemiring A] [Module R A] [NonUnitalNonAssocSemiring B] [Module R B]

variable [NonUnitalNonAssocSemiring C] [Module R C] [FunLike F A B] [NonUnitalAlgHomClass F R A B]

theorem range_comp_le_range (f : A →ₙₐ[R] B) (g : B →ₙₐ[R] C) :
    NonUnitalAlgHom.range (g.comp f) ≤ NonUnitalAlgHom.range g := SetLike.coe_mono (Set.range_comp_subset_range f g)

