import Mathlib

open scoped LaurentPolynomial

variable {R S : Type*}

variable [Semiring R]

theorem invOf_T (n : ℤ) : ⅟(LaurentPolynomial.T n : R[T;T⁻¹]) = LaurentPolynomial.T (-n) := rfl

