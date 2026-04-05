import Mathlib

variable {R S : Type*}

variable [DivisionMonoid R] [HasDistribNeg R] {a b : R}

theorem one_div_neg_eq_neg_one_div (a : R) : 1 / -a = -(1 / a) := calc
    1 / -a = 1 / (-1 * a) := by rw [neg_eq_neg_one_mul]
    _ = 1 / a * (1 / -1) := by rw [one_div_mul_one_div_rev]
    _ = 1 / a * -1 := by rw [one_div_neg_one_eq_neg_one]
    _ = -(1 / a) := by rw [mul_neg, mul_one]

