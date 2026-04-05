import Mathlib

variable {R : Type u}

variable [Monoid R] [HasDistribNeg R]

theorem neg_one_sq : (-1 : R) ^ 2 = 1 := by simp [neg_sq, one_pow]

alias neg_pow_two := neg_sq

alias neg_one_pow_two := neg_one_sq

