import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem sInf_toSubmonoid (s : Set (Subring R)) :
    (sInf s).toSubmonoid = ⨅ t ∈ s, t.toSubmonoid := mk'_toSubmonoid _ _

