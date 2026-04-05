import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem coe_inf (p p' : Subring R) : ((p ⊓ p' : Subring R) : Set R) = (p : Set R) ∩ p' := rfl

