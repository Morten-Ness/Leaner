import Mathlib

variable {R S : Type*}

variable [Semiring R]

set_option backward.isDefEq.respectTransparency false in
theorem support_C_mul_T (a : R) (n : ℤ) : Finsupp.support (Polynomial.C a * LaurentPolynomial.T n) ⊆ {n} := by
  rw [← LaurentPolynomial.single_eq_C_mul_T]
  exact support_single_subset

