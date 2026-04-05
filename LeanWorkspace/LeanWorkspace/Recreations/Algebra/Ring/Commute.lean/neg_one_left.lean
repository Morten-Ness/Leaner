import Mathlib

variable {R : Type u}

variable [MulOneClass R] [HasDistribNeg R]

theorem neg_one_left (a : R) : Commute (-1) a := SemiconjBy.neg_one_left a

