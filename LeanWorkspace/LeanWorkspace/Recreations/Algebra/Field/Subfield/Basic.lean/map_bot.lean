import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem map_bot (f : K →+* L) : (⊥ : Subfield K).map f = ⊥ := (Subfield.gc_map_comap f).l_bot

