import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem closure_singleton_one : Subring.closure {(1 : R)} = ⊥ := mod_cast Subring.closure_singleton_natCast 1

