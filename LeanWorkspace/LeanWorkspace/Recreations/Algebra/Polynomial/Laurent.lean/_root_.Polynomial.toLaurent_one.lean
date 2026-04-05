import Mathlib

open scoped Polynomial LaurentPolynomial

variable {R S : Type*}

variable [Semiring R]

theorem _root_.Polynomial.toLaurent_one : (Polynomial.toLaurent : R[X] → R[T;T⁻¹]) 1 = 1 := map_one Polynomial.toLaurent

