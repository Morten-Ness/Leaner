import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable {s : Subfield K}

variable {L : Type v} [Semiring L]

theorem mem_eqLocusField {f g : K →+* L} {x : K} : x ∈ f.eqLocusField g ↔ f x = g x := Iff.rfl

