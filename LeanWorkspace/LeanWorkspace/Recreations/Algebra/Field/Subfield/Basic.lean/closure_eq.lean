import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem closure_eq (s : Subfield K) : Subfield.closure (s : Set K) = s := (Subfield.gi K).l_u_eq s

