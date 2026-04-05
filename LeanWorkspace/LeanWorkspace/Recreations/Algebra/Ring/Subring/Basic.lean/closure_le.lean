import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem closure_le {s : Set R} {t : Subring R} : Subring.closure s ≤ t ↔ s ⊆ t := ⟨Set.Subset.trans Subring.subset_closure, fun h => sInf_le h⟩

