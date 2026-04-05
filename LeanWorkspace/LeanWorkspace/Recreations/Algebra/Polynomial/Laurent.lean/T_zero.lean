import Mathlib

open scoped LaurentPolynomial

variable {R S : Type*}

variable [Semiring R]

theorem T_zero : (LaurentPolynomial.T 0 : R[T;T⁻¹]) = 1 := rfl

