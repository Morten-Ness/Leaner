import Mathlib

variable {R : Type v} [NonAssocSemiring R] [StarRing R]

theorem coe_copy (S : StarSubsemiring R) (s : Set R) (hs : s = ↑S) : (S.copy s hs : Set R) = s := rfl

