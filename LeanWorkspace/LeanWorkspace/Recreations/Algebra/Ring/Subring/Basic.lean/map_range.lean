import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

variable (g : S →+* T) (f : R →+* S)

theorem map_range : f.range.map g = (g.comp f).range := by
  simpa only [RingHom.range_eq_map] using Subring.map_map (⊤ : Subring R) g f

