import Mathlib

variable {F : Type v'} {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [NonUnitalNonAssocSemiring A] [Module R A] [NonUnitalNonAssocSemiring B] [Module R B]

variable [NonUnitalNonAssocSemiring C] [Module R C] [FunLike F A B] [NonUnitalAlgHomClass F R A B]

theorem injective_codRestrict (f : F) (S : NonUnitalSubalgebra R B) (hf : ∀ x : A, f x ∈ S) :
    Function.Injective (NonUnitalAlgHom.codRestrict f S hf) ↔ Function.Injective f := ⟨fun H _x _y hxy => H <| Subtype.ext hxy, fun H _x _y hxy => H (congr_arg Subtype.val hxy :)⟩

