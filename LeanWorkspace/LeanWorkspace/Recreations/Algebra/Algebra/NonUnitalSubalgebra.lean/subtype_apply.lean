import Mathlib

variable {S R A : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

variable [SetLike S A] [NonUnitalSubsemiringClass S A] [hSR : SMulMemClass S R A] (s : S)

theorem subtype_apply (x : s) : NonUnitalSubalgebraClass.subtype s x = x := rfl

