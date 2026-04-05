import Mathlib

variable {R S : Type*}

variable [CommSemiring R] {S : Type*} [CommSemiring S] (f : R →+* S) (x : Sˣ)

theorem eval₂_C_mul_T_neg_n (r : R) (n : ℕ) : LaurentPolynomial.eval₂ f x (Polynomial.C r * LaurentPolynomial.T (-n)) = f r * x⁻¹ ^ n := by
  rw [map_mul, LaurentPolynomial.eval₂_T_neg_n, LaurentPolynomial.eval₂_C]

