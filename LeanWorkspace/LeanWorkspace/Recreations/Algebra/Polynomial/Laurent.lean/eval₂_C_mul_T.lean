import Mathlib

variable {R S : Type*}

variable [CommSemiring R] {S : Type*} [CommSemiring S] (f : R →+* S) (x : Sˣ)

theorem eval₂_C_mul_T (r : R) (n : ℤ) : LaurentPolynomial.eval₂ f x (Polynomial.C r * LaurentPolynomial.T n) = f r * (x ^ n).val := by
  simp

