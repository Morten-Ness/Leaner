import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem closure_mono ⦃s t : Set R⦄ (h : s ⊆ t) : Subring.closure s ≤ Subring.closure t := Subring.closure_le.2 <| Set.Subset.trans h Subring.subset_closure

