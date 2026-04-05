import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem closure_union (s t : Set R) : Subring.closure (s ∪ t) = Subring.closure s ⊔ Subring.closure t := (Subring.gi R).gc.l_sup

