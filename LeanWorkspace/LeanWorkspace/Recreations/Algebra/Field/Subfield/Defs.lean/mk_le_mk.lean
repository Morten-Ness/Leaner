import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem mk_le_mk {S S' : Subring K} (h h') : (⟨S, h⟩ : Subfield K) ≤ (⟨S', h'⟩ : Subfield K) ↔
    S ≤ S' := Iff.rfl

