import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem coe_centralizer {R} [Semiring R] (s : Set R) : (Subsemiring.centralizer s : Set R) = s.centralizer := rfl

