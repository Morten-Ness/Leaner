import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem closure_eq_of_le {s : Set K} {t : Subfield K} (h₁ : s ⊆ t) (h₂ : t ≤ Subfield.closure s) :
    Subfield.closure s = t := le_antisymm (Subfield.closure_le.2 h₁) h₂

