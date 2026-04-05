import Mathlib

variable {M : Type*}

theorem fg_iff [Mul M] {I : SemigroupIdeal M} : I.FG ↔ ∃ (s : Finset M), I = closure s := SubMulAction.fg_iff

