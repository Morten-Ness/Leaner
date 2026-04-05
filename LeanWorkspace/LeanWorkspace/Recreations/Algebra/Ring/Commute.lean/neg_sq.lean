import Mathlib

variable {R : Type u}

variable [Monoid R] [HasDistribNeg R]

theorem neg_sq (a : R) : (-a) ^ 2 = a ^ 2 := by simp [sq]

