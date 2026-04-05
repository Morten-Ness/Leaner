import Mathlib

variable [MulZeroClass R] {a b : R}

theorem not_isLeftRegular_zero [nR : Nontrivial R] : ¬IsLeftRegular (0 : R) := not_isLeftRegular_zero_iff.mpr nR

