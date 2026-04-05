import Mathlib

variable {F : Type v'} {R' : Type u'} {R : Type u}

variable {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [NonUnitalNonAssocSemiring A] [Module R A] [Star A]

variable [NonUnitalNonAssocSemiring B] [Module R B] [Star B]

variable [NonUnitalNonAssocSemiring C] [Module R C] [Star C]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B]

theorem subtype_comp_codRestrict (f : F) (S : NonUnitalStarSubalgebra R B) (hf : ∀ x : A, f x ∈ S) :
    (NonUnitalStarSubalgebraClass.subtype S).comp (NonUnitalStarAlgHom.codRestrict f S hf) = f := NonUnitalStarAlgHom.ext fun _ => rfl

