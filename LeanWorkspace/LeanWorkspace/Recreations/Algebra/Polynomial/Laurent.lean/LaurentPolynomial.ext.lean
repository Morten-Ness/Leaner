import Mathlib

open scoped LaurentPolynomial

variable {R S : Type*}

theorem LaurentPolynomial.ext [Semiring R] {p q : R[T;T⁻¹]} (h : ∀ a, p a = q a) : p = q := Finsupp.ext h

