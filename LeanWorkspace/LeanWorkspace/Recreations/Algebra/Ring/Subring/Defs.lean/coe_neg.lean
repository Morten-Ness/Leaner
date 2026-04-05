import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable (s : Subring R)

theorem coe_neg (x : s) : (↑(-x) : R) = -↑x := rfl

