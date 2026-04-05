import Mathlib

variable [MulZeroClass R] {a b : R}

theorem not_isRegular_zero [Nontrivial R] : ¬IsRegular (0 : R) := fun h => IsRegular.ne_zero h rfl

