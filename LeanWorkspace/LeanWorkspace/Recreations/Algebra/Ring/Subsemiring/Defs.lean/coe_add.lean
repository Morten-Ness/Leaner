import Mathlib

variable {R : Type u} {S : Type v} [NonAssocSemiring R]

variable [NonAssocSemiring S]

variable (s : Subsemiring R)

theorem coe_add (x y : s) : ((x + y : s) : R) = (x + y : R) := rfl

