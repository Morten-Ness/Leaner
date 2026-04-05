import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem closure_insert_one (s : Set R) : Subring.closure (insert 1 s) = Subring.closure s := mod_cast Subring.closure_insert_natCast 1 s

