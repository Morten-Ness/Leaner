import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable (s : Subring R)

theorem coe_one : ((1 : s) : R) = 1 := rfl

