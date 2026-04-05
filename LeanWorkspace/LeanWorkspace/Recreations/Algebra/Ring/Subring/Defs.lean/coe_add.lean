import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable (s : Subring R)

theorem coe_add (x y : s) : (↑(x + y) : R) = ↑x + ↑y := rfl

