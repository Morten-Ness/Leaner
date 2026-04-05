import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable (s : Subring R)

theorem coe_zero : ((0 : s) : R) = 0 := rfl

