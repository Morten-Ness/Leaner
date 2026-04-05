import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem sInf_toAddSubgroup (s : Set (Subring R)) :
    (sInf s).toAddSubgroup = ⨅ t ∈ s, Subring.toAddSubgroup t := mk'_toAddSubgroup _ _

