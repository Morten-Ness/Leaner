import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem coe_inf (p p' : Subfield K) : ((p ⊓ p' : Subfield K) : Set K) = p.carrier ∩ p'.carrier := rfl

