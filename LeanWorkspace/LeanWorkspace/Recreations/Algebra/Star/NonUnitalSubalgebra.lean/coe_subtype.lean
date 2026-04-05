import Mathlib

variable {F : Type v'} {R' : Type u'} {R : Type u}

variable {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R] [NonUnitalNonAssocSemiring A]

variable [Star A] [Module R A]

variable {S : Type w''} [SetLike S A] [NonUnitalSubsemiringClass S A]

variable [hSR : SMulMemClass S R A] [StarMemClass S A] (s : S)

theorem coe_subtype : (NonUnitalStarSubalgebraClass.subtype s : s → A) = Subtype.val := rfl

