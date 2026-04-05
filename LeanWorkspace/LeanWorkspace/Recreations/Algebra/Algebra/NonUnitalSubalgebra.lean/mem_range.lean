import Mathlib

variable {F : Type v'} {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [NonUnitalNonAssocSemiring A] [Module R A] [NonUnitalNonAssocSemiring B] [Module R B]

variable [NonUnitalNonAssocSemiring C] [Module R C] [FunLike F A B] [NonUnitalAlgHomClass F R A B]

theorem mem_range (φ : F) {y : B} :
    y ∈ (NonUnitalAlgHom.range φ : NonUnitalSubalgebra R B) ↔ ∃ x : A, φ x = y := NonUnitalRingHom.mem_srange

