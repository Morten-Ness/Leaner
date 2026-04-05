import Mathlib

variable {R : Type u} {S : Type v} [NonAssocSemiring R]

variable [NonAssocSemiring S]

theorem Subsemiring.toNonUnitalSubsemiring_toSubsemiring (S : Subsemiring R) :
    S.toNonUnitalSubsemiring.toSubsemiring S.one_mem = S := rfl

