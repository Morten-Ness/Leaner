import Mathlib

variable {R S : Type*}

variable [CommSemiring R] {S : Type*} [CommSemiring S] (f : R →+* S) (x : Sˣ)

theorem eval₂_T_n (n : ℕ) : LaurentPolynomial.eval₂ f x (LaurentPolynomial.T n) = x ^ n := by
  rw [← Polynomial.toLaurent_X_pow, LaurentPolynomial.eval₂_toLaurent, eval₂_X_pow]

