import Mathlib

variable {R S : Type*}

variable [DivisionMonoid R] [HasDistribNeg R] {a b : R}

theorem neg_div_neg_eq (a b : R) : -a / -b = a / b := by rw [div_neg_eq_neg_div, neg_div, neg_neg]

