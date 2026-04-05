import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem map_comap_eq_self_of_surjective
    {f : R →+* S} (hf : Function.Surjective f) (t : Subring S) : (t.comap f).map f = t := Subring.map_comap_eq_self <| by simp [hf]

