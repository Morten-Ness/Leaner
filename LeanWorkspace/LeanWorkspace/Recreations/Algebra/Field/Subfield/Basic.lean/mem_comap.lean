import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable (s t : Subfield K)

variable (f : K →+* L)

theorem mem_comap {s : Subfield L} {f : K →+* L} {x : K} : x ∈ s.comap f ↔ f x ∈ s := Iff.rfl

