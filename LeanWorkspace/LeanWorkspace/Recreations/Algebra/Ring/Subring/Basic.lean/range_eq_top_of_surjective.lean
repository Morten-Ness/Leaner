import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

variable {s : Subring R}

theorem range_eq_top_of_surjective (f : R →+* S) (hf : Function.Surjective f) :
    f.range = (⊤ : Subring S) := RingHom.range_eq_top.2 hf

