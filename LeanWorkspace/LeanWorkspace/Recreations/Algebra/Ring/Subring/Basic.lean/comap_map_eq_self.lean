import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem comap_map_eq_self {f : R →+* S} {s : Subring R}
    (h : f ⁻¹' {0} ⊆ s) : (s.map f).comap f = s := by
  convert Subring.comap_map_eq f s
  rwa [left_eq_sup, Subring.closure_le]

