import Mathlib

variable {R S : Type*}

variable [DivisionMonoid R] [HasDistribNeg R] {a b : R}

theorem div_neg_eq_neg_div (a b : R) : b / -a = -(b / a) := calc
    b / -a = b * (1 / -a) := by rw [← inv_eq_one_div, division_def]
    _ = b * -(1 / a) := by rw [one_div_neg_eq_neg_one_div]
    _ = -(b * (1 / a)) := by rw [neg_mul_eq_mul_neg]
    _ = -(b / a) := by rw [mul_one_div]

