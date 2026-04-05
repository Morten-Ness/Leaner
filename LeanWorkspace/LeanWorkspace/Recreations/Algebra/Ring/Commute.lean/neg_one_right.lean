import Mathlib

variable {R : Type u}

variable [MulOneClass R] [HasDistribNeg R]

theorem neg_one_right (a : R) : Commute a (-1) := SemiconjBy.neg_one_right a

