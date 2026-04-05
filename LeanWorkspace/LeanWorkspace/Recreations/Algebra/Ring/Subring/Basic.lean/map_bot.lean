import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem map_bot (f : R →+* S) : (⊥ : Subring R).map f = ⊥ := (Subring.gc_map_comap f).l_bot

