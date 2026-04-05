import Mathlib

variable {R : Type u}

variable [MulOneClass R] [HasDistribNeg R]

theorem neg_one_right (a : R) : SemiconjBy a (-1) (-1) := by simp

