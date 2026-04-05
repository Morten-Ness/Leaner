import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable (s : Subring R)

theorem coe_toSubmonoid (s : Subring R) : (s.toSubmonoid : Set R) = s := rfl

