import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable (s : Subring R)

theorem coe_toSubsemiring (s : Subring R) : (s.toSubsemiring : Set R) = s := rfl

