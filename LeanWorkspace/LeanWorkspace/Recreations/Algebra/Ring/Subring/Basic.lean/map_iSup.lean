import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem map_iSup {ι : Sort*} (f : R →+* S) (s : ι → Subring R) :
    (iSup s).map f = ⨆ i, (s i).map f := (Subring.gc_map_comap f).l_iSup

