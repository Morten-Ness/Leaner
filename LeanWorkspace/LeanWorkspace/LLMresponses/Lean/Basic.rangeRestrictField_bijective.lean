FAIL
import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable {s : Subfield K}

theorem rangeRestrictField_bijective (f : K →+* L) : Function.Bijective (RingHom.rangeRestrictField f) := by
  constructor
  · intro x y h
    apply f.injective
    exact congrArg Subtype.val h
  · intro y
    rcases y.2 with ⟨x, rfl⟩
    refine ⟨x, ?_⟩
    rfl
