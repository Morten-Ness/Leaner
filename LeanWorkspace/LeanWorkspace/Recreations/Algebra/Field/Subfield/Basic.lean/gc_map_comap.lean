import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable (s t : Subfield K)

variable (f : K →+* L)

theorem gc_map_comap (f : K →+* L) : GaloisConnection (Subfield.map f) (Subfield.comap f) := fun _ _ =>
  Subfield.map_le_iff_le_comap

