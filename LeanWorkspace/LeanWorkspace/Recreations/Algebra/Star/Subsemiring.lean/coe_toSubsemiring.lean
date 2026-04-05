import Mathlib

variable {R : Type v} [NonAssocSemiring R] [StarRing R]

theorem coe_toSubsemiring (S : StarSubsemiring R) : (S.toSubsemiring : Set R) = S := rfl

