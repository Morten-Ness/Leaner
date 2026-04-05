import Mathlib

variable [MulZeroClass R] {a b : R}

theorem not_isRightRegular_zero [nR : Nontrivial R] : ¬IsRightRegular (0 : R) := not_isRightRegular_zero_iff.mpr nR

