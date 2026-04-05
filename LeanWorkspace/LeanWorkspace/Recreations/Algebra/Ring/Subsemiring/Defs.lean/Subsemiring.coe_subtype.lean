import Mathlib

variable {R : Type u} {S : Type v} [NonAssocSemiring R]

variable [NonAssocSemiring S]

variable (s : Subsemiring R)

theorem coe_subtype : ⇑s.subtype = ((↑) : s → R) := rfl

