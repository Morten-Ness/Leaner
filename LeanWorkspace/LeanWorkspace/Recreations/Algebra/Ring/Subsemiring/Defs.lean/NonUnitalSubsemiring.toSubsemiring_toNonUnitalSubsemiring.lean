import Mathlib

variable {R : Type u} {S : Type v} [NonAssocSemiring R]

variable [NonAssocSemiring S]

theorem NonUnitalSubsemiring.toSubsemiring_toNonUnitalSubsemiring (S : NonUnitalSubsemiring R) (h1) :
    (NonUnitalSubsemiring.toSubsemiring S h1).toNonUnitalSubsemiring = S := rfl

