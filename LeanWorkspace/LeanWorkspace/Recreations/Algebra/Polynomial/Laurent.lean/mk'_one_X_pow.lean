import Mathlib

open scoped Polynomial LaurentPolynomial

variable {R S : Type*}

variable [CommSemiring R] {S : Type*} [CommSemiring S] (f : R →+* S) (x : Sˣ)

theorem mk'_one_X_pow (n : ℕ) :
    IsLocalization.mk' R[T;T⁻¹] 1 (⟨Polynomial.X^n, n, rfl⟩ : Submonoid.powers (Polynomial.X : R[X])) = LaurentPolynomial.T (-n) := by
  rw [LaurentPolynomial.mk'_eq 1 n, toLaurent_one, one_mul]

