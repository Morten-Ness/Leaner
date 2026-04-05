import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem closure_insert_zero (s : Set R) : Subring.closure (insert 0 s) = Subring.closure s := mod_cast Subring.closure_insert_natCast 0 s

