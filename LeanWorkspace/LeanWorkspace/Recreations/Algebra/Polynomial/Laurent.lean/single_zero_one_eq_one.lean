import Mathlib

open scoped LaurentPolynomial

variable {R S : Type*}

variable [Semiring R]

theorem single_zero_one_eq_one : (.single 0 1 : R[T;T⁻¹]) = (1 : R[T;T⁻¹]) := rfl

