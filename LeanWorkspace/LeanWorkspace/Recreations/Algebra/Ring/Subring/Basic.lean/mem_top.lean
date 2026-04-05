import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

variable (s : Subring R)

theorem mem_top (x : R) : x ∈ (⊤ : Subring R) := Set.mem_univ x

