import Mathlib

open scoped LaurentPolynomial

variable {R S : Type*}

variable [Semiring R]

theorem isUnit_T (n : ℤ) : IsUnit (LaurentPolynomial.T n : R[T;T⁻¹]) := isUnit_of_invertible _

