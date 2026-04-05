import Mathlib

open scoped Polynomial LaurentPolynomial

variable {R S : Type*}

variable [CommSemiring R] {S : Type*} [CommSemiring S] (f : R →+* S) (x : Sˣ)

theorem mk'_one_X :
    IsLocalization.mk' R[T;T⁻¹] 1 (⟨Polynomial.X, 1, pow_one Polynomial.X⟩ : Submonoid.powers (Polynomial.X : R[X])) = LaurentPolynomial.T (-1) := by
  convert LaurentPolynomial.mk'_one_X_pow 1
  exact (pow_one Polynomial.X).symm

