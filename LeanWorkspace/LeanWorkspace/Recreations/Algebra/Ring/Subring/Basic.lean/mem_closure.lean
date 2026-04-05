import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem mem_closure {x : R} {s : Set R} : x ∈ Subring.closure s ↔ ∀ S : Subring R, s ⊆ S → x ∈ S := Subring.mem_sInf

