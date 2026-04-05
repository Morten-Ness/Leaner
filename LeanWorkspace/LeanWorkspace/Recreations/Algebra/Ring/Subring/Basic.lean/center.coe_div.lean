import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

variable {K : Type u} [DivisionRing K]

theorem center.coe_div (a b : Subring.center K) : ((a / b : Subring.center K) : K) = (a : K) / (b : K) := rfl

