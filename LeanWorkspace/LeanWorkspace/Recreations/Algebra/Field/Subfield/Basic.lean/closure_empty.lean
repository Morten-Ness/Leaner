import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem closure_empty : Subfield.closure (∅ : Set K) = ⊥ := (Subfield.gi K).gc.l_bot

