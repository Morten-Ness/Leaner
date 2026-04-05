import Mathlib

variable {F : Type v'} {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [NonUnitalNonAssocSemiring A] [Module R A] [NonUnitalNonAssocSemiring B] [Module R B]

variable [NonUnitalNonAssocSemiring C] [Module R C] [FunLike F A B] [NonUnitalAlgHomClass F R A B]

theorem coe_range (φ : F) :
    ((NonUnitalAlgHom.range φ : NonUnitalSubalgebra R B) : Set B) = Set.range (φ : A → B) := by
  ext
  rw [SetLike.mem_coe, NonUnitalAlgHom.mem_range, Set.mem_range]

