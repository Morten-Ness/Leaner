import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable (s t : Subfield K)

variable (f : K →+* L)

theorem comap_comap (s : Subfield M) (g : L →+* M) (f : K →+* L) :
    (s.comap g).comap f = s.comap (g.comp f) := rfl

