import Mathlib

open scoped Polynomial

variable {R S : Type*}

variable [CommSemiring R] {S : Type*} [CommSemiring S] (f : R →+* S) (x : Sˣ)

theorem eval₂_toLaurent (p : R[X]) : LaurentPolynomial.eval₂ f x (toLaurent p) = Polynomial.eval₂ f x p := by
  unfold LaurentPolynomial.eval₂
  rw [← LaurentPolynomial.algebraMap_eq_toLaurent, IsLocalization.lift_eq, coe_eval₂RingHom]

