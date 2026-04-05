import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable (s : Subring R)

theorem coe_intCast (n : ℤ) : ((n : s) : R) = n := rfl

