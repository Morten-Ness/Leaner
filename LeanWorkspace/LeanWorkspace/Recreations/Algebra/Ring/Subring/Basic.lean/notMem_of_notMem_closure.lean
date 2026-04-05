import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem notMem_of_notMem_closure {s : Set R} {P : R} (hP : P ∉ Subring.closure s) : P ∉ s := fun h =>
  hP (Subring.subset_closure h)

