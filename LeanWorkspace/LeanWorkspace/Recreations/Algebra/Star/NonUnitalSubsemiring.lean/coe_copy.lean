import Mathlib

variable {A : Type v} {B : Type w} {C : Type w'}

variable {R : Type v} [NonUnitalNonAssocSemiring R] [StarRing R]

theorem coe_copy (S : NonUnitalStarSubsemiring R) (s : Set R) (hs : s = ↑S) :
    (S.copy s hs : Set R) = s := rfl

