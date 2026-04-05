import Mathlib

variable {R : Type u} {S : Type v} [NonAssocSemiring R]

variable [NonAssocSemiring S]

theorem coe_toNonUnitalSubsemiring (S : Subsemiring R) : (S.toNonUnitalSubsemiring : Set R) = S := rfl

