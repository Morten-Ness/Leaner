import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

variable {K : Type u} [DivisionRing K]

theorem center.coe_inv (a : Subring.center K) : ((a⁻¹ : Subring.center K) : K) = (a : K)⁻¹ := rfl

