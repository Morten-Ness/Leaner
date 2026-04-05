import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem closure_singleton_intCast (n : ℤ) : Subring.closure {(n : R)} = ⊥ := bot_unique <| Subring.closure_le.2 <| Set.singleton_subset_iff.mpr <| intCast_mem _ _

