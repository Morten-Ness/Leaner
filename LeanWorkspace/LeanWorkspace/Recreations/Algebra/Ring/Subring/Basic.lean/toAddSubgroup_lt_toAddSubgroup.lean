import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

variable {s t : Subring R}

theorem toAddSubgroup_lt_toAddSubgroup (hst : s < t) : s.toAddSubgroup < t.toAddSubgroup := hst

