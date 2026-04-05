import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem comap_equiv_eq_map_symm (f : R ≃+* S) (K : Subring S) :
    K.comap (f : R →+* S) = K.map f.symm := (Subring.map_equiv_eq_comap_symm f.symm K).symm

