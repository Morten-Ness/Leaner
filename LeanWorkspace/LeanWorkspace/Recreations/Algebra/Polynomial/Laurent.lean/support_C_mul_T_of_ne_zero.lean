import Mathlib

variable {R S : Type*}

variable [Semiring R]

set_option backward.isDefEq.respectTransparency false in
theorem support_C_mul_T_of_ne_zero {a : R} (a0 : a ≠ 0) (n : ℤ) :
    Finsupp.support (Polynomial.C a * LaurentPolynomial.T n) = {n} := by
  rw [← LaurentPolynomial.single_eq_C_mul_T]
  exact support_single_ne_zero _ a0

