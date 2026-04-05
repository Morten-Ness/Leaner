import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem closure_singleton_natCast (n : ℕ) : Subring.closure {(n : R)} = ⊥ := mod_cast Subring.closure_singleton_intCast n

