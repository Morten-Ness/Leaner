import Mathlib

open scoped LaurentPolynomial

variable {R S : Type*}

variable [Semiring R]

theorem _root_.Polynomial.toLaurent_C_mul_T (n : ℕ) (r : R) :
    (toLaurent (Polynomial.monomial n r) : R[T;T⁻¹]) = Polynomial.C r * LaurentPolynomial.T n := by simp [toLaurent]

