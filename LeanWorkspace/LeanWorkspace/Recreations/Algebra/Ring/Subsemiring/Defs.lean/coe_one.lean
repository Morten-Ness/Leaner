import Mathlib

variable {R : Type u} {S : Type v} [NonAssocSemiring R]

variable [NonAssocSemiring S]

variable (s : Subsemiring R)

theorem coe_one : ((1 : s) : R) = (1 : R) := rfl

