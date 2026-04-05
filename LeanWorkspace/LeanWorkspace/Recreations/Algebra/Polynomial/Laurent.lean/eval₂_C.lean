import Mathlib

variable {R S : Type*}

variable [CommSemiring R] {S : Type*} [CommSemiring S] (f : R →+* S) (x : Sˣ)

theorem eval₂_C (r : R) : LaurentPolynomial.eval₂ f x (Polynomial.C r) = f r := by
  rw [← toLaurent_C, LaurentPolynomial.eval₂_toLaurent, Polynomial.eval₂_C]

