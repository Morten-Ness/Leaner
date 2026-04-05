import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem closure_union (s t : Set K) : Subfield.closure (s ∪ t) = Subfield.closure s ⊔ Subfield.closure t := (Subfield.gi K).gc.l_sup

