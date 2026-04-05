import Mathlib

variable {R : Type u}

variable [MulOneClass R] [HasDistribNeg R]

theorem neg_one_left (x : R) : SemiconjBy (-1) x x := by simp

