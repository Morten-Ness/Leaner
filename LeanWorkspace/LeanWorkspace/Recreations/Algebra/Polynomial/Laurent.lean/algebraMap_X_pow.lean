import Mathlib

open scoped Polynomial LaurentPolynomial

variable {R S : Type*}

variable [CommSemiring R] {S : Type*} [CommSemiring S] (f : R →+* S) (x : Sˣ)

theorem algebraMap_X_pow (n : ℕ) : algebraMap R[X] R[T;T⁻¹] (Polynomial.X ^ n) = LaurentPolynomial.T n := Polynomial.toLaurent_X_pow n

