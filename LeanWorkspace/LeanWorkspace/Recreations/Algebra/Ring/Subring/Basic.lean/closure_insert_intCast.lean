import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem closure_insert_intCast (n : ℤ) (s : Set R) : Subring.closure (insert (n : R) s) = Subring.closure s := by
  rw [Set.insert_eq, Subring.closure_union]
  simp

