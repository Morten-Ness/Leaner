import Mathlib

variable {R S : Type*}

variable [DivisionMonoid R] [HasDistribNeg R] {a b : R}

theorem one_div_neg_one_eq_neg_one : (1 : R) / -1 = -1 := have : -1 * -1 = (1 : R) := by rw [neg_mul_neg, one_mul]
  Eq.symm (eq_one_div_of_mul_eq_one_right this)

