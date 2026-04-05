import Mathlib

open scoped Polynomial

variable {R S : Type*}

variable [Semiring R]

theorem _root_.Polynomial.trunc_toLaurent (f : R[X]) : LaurentPolynomial.trunc (toLaurent f) = f := LaurentPolynomial.leftInverse_trunc_toLaurent _

