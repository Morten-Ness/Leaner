import Mathlib

variable {R : Type u} {S : Type v} [NonAssocSemiring R]

variable [NonAssocSemiring S]

variable (s : Subsemiring R)

theorem coe_top : ((⊤ : Subsemiring R) : Set R) = Set.univ := rfl

