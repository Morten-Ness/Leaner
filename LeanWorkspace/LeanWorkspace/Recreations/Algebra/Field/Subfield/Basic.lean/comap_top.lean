import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem comap_top (f : K →+* L) : (⊤ : Subfield L).comap f = ⊤ := (Subfield.gc_map_comap f).u_top

