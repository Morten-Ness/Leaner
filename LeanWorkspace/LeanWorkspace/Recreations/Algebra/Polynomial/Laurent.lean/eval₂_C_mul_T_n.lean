import Mathlib

variable {R S : Type*}

variable [CommSemiring R] {S : Type*} [CommSemiring S] (f : R →+* S) (x : Sˣ)

theorem eval₂_C_mul_T_n (r : R) (n : ℕ) : LaurentPolynomial.eval₂ f x (Polynomial.C r * LaurentPolynomial.T n) = f r * x ^ n := by
  rw [← Polynomial.toLaurent_C_mul_T, LaurentPolynomial.eval₂_toLaurent, eval₂_monomial]

