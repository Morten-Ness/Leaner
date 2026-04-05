import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem closure_empty : Subring.closure (∅ : Set R) = ⊥ := (Subring.gi R).gc.l_bot

