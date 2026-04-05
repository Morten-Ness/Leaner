import Mathlib

open scoped LaurentPolynomial

variable {R S : Type*}

variable [Semiring R]

theorem C_eq_algebraMap {R : Type*} [CommSemiring R] (r : R) : Polynomial.C r = algebraMap R R[T;T⁻¹] r := rfl

