import Mathlib

variable {S R A : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

variable [SetLike S A] [NonUnitalSubsemiringClass S A] [hSR : SMulMemClass S R A] (s : S)

theorem coe_subtype : (NonUnitalSubalgebraClass.subtype s : s → A) = ((↑) : s → A) := rfl

