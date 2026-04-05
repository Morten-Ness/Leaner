import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem comap_top (f : R →+* S) : (⊤ : Subring S).comap f = ⊤ := (Subring.gc_map_comap f).u_top

