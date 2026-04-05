import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem closure_iUnion {ι} (s : ι → Set R) : Subring.closure (⋃ i, s i) = ⨆ i, Subring.closure (s i) := (Subring.gi R).gc.l_iSup

