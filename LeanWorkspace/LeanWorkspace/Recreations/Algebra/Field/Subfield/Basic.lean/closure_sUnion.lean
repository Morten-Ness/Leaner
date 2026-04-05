import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem closure_sUnion (s : Set (Set K)) : Subfield.closure (⋃₀ s) = ⨆ t ∈ s, Subfield.closure t := (Subfield.gi K).gc.l_sSup

