import Mathlib

variable {F : Type v'} {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [NonUnitalNonAssocSemiring A] [Module R A] [NonUnitalNonAssocSemiring B] [Module R B]

variable [NonUnitalNonAssocSemiring C] [Module R C] [FunLike F A B] [NonUnitalAlgHomClass F R A B]

theorem range_comp (f : A →ₙₐ[R] B) (g : B →ₙₐ[R] C) :
    NonUnitalAlgHom.range (g.comp f) = (NonUnitalAlgHom.range f).map g := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨f y, ⟨y, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    exact ⟨z, rfl⟩
