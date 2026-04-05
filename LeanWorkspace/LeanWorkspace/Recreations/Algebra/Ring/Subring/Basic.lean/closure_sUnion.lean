import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem closure_sUnion (s : Set (Set R)) : Subring.closure (⋃₀ s) = ⨆ t ∈ s, Subring.closure t := (Subring.gi R).gc.l_sSup

