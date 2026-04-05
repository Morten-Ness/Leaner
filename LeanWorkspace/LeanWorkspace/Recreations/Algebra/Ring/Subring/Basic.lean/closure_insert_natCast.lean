import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem closure_insert_natCast (n : ℕ) (s : Set R) : Subring.closure (insert (n : R) s) = Subring.closure s := mod_cast Subring.closure_insert_intCast n s

