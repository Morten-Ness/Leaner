import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

variable (g : S →+* T) (f : R →+* S)

theorem range_eq_map (f : R →+* S) : f.range = Subring.map f ⊤ := by
  ext
  simp

