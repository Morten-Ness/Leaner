import Mathlib

open scoped LaurentPolynomial

variable {R S : Type*}

variable [Semiring R]

theorem T_mul (n : ℤ) (f : R[T;T⁻¹]) : LaurentPolynomial.T n * f = f * LaurentPolynomial.T n := (LaurentPolynomial.commute_T n f).eq

