import Mathlib

open scoped LaurentPolynomial

variable {R S : Type*}

variable [Semiring R]

theorem degree_zero : LaurentPolynomial.degree (0 : R[T;T⁻¹]) = ⊥ := rfl

