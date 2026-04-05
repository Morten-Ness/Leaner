import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem map_comap_eq_self
    {f : R →+* S} {t : Subring S} (h : t ≤ f.range) : (t.comap f).map f = t := by
  simpa only [inf_of_le_left h] using Subring.map_comap_eq f t

