import Mathlib

variable {R : Type u} {S : Type v} [NonAssocSemiring R]

variable [NonAssocSemiring S]

variable (s : Subsemiring R)

theorem subtype_injective :
    Function.Injective s.subtype := Subtype.coe_injective

