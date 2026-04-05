import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem mem_closure_of_mem {s : Set R} {x : R} (hx : x ∈ s) : x ∈ Subring.closure s := Subring.subset_closure hx

