import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem closure_univ : Subring.closure (Set.univ : Set R) = ⊤ := @Subring.coe_top R _ ▸ Subring.closure_eq ⊤

