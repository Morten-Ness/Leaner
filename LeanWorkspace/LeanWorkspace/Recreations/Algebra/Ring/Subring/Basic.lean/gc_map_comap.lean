import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

variable (s : Subring R)

theorem gc_map_comap (f : R →+* S) : GaloisConnection (Subring.map f) (Subring.comap f) := fun _ _ =>
  Subring.map_le_iff_le_comap

