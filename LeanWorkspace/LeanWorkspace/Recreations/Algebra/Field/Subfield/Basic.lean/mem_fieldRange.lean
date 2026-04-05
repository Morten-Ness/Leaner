import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable (g : L →+* M) (f : K →+* L)

theorem mem_fieldRange {f : K →+* L} {y : L} : y ∈ f.fieldRange ↔ ∃ x, f x = y := Iff.rfl

