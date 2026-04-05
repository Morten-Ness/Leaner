import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem closure_singleton_zero : Subring.closure {(0 : R)} = ⊥ := mod_cast Subring.closure_singleton_natCast 0

