import Mathlib

variable {R S : Type*}

variable [DivisionMonoid R] [HasDistribNeg R] {a b : R}

theorem div_neg (a : R) : a / -b = -(a / b) := by rw [← div_neg_eq_neg_div]

