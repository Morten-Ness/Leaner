import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem closure_iUnion {ι} (s : ι → Set K) : Subfield.closure (⋃ i, s i) = ⨆ i, Subfield.closure (s i) := (Subfield.gi K).gc.l_iSup

