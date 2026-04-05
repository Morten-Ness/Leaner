import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable (g : L →+* M) (f : K →+* L)

theorem fieldRange_eq_map : f.fieldRange = Subfield.map f ⊤ := by
  ext
  simp

