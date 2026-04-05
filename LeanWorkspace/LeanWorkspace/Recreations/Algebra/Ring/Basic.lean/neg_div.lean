import Mathlib

variable {R S : Type*}

variable [DivisionMonoid R] [HasDistribNeg R] {a b : R}

theorem neg_div (a b : R) : -b / a = -(b / a) := by
  rw [neg_eq_neg_one_mul, mul_div_assoc, ← neg_eq_neg_one_mul]

