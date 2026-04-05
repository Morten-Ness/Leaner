import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable {s : Subfield K}

theorem rangeRestrictField_bijective (f : K →+* L) : Function.Bijective (RingHom.rangeRestrictField f) := (Equiv.ofInjective f f.injective).bijective

