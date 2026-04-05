import Mathlib

open scoped Polynomial LaurentPolynomial

variable {R S : Type*}

variable [Semiring R]

theorem _root_.Polynomial.toLaurent_injective :
    Function.Injective (Polynomial.toLaurent : R[X] → R[T;T⁻¹]) := LaurentPolynomial.leftInverse_trunc_toLaurent.injective

