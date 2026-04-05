import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable (g : L →+* M) (f : K →+* L)

theorem map_fieldRange : f.fieldRange.map g = (g.comp f).fieldRange := by
  simpa only [RingHom.fieldRange_eq_map] using Subfield.map_map (⊤ : Subfield K) g f

