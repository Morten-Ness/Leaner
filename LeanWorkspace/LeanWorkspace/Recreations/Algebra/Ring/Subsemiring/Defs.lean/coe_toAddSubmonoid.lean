import Mathlib

variable {R : Type u} {S : Type v} [NonAssocSemiring R]

variable [NonAssocSemiring S]

variable (s : Subsemiring R)

theorem coe_toAddSubmonoid (s : Subsemiring R) : (s.toAddSubmonoid : Set R) = s := rfl

