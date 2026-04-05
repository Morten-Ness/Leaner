import Mathlib

variable {F : Type v'} {R' : Type u'} {R : Type u}

variable {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [NonUnitalNonAssocSemiring A] [Module R A] [Star A]

variable [NonUnitalNonAssocSemiring B] [Module R B] [Star B]

variable [NonUnitalNonAssocSemiring C] [Module R C] [Star C]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B]

theorem injective_codRestrict (f : F) (S : NonUnitalStarSubalgebra R B) (hf : ∀ x : A, f x ∈ S) :
    Function.Injective (NonUnitalStarAlgHom.codRestrict f S hf) ↔ Function.Injective f := ⟨fun H _x _y hxy => H <| Subtype.ext hxy, fun H _x _y hxy => H (congr_arg Subtype.val hxy :)⟩

