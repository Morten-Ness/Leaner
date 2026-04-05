import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem coe_sInf (S : Set (Subfield K)) : ((sInf S : Subfield K) : Set K) = ⋂ s ∈ S, ↑s := show ((sInf (Subfield.toSubring '' S) : Subring K) : Set K) = ⋂ s ∈ S, ↑s by simp

