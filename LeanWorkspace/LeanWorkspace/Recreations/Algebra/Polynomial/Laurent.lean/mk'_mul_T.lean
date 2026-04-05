import Mathlib

open scoped Polynomial LaurentPolynomial

variable {R S : Type*}

variable [CommSemiring R] {S : Type*} [CommSemiring S] (f : R →+* S) (x : Sˣ)

theorem mk'_mul_T (p : R[X]) (n : ℕ) :
    IsLocalization.mk' R[T;T⁻¹] p (⟨Polynomial.X^n, n, rfl⟩ : Submonoid.powers (Polynomial.X : R[X])) * LaurentPolynomial.T n =
      toLaurent p := by
  rw [← toLaurent_X_pow, ← LaurentPolynomial.algebraMap_eq_toLaurent, IsLocalization.mk'_spec,
    LaurentPolynomial.algebraMap_eq_toLaurent]

