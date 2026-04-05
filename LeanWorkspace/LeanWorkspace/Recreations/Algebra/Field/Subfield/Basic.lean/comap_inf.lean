import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem comap_inf (s t : Subfield L) (f : K →+* L) : (s ⊓ t).comap f = s.comap f ⊓ t.comap f := (Subfield.gc_map_comap f).u_inf

