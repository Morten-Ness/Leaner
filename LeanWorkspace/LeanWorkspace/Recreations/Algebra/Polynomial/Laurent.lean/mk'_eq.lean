import Mathlib

open scoped Polynomial LaurentPolynomial

variable {R S : Type*}

variable [CommSemiring R] {S : Type*} [CommSemiring S] (f : R →+* S) (x : Sˣ)

theorem mk'_eq (p : R[X]) (n : ℕ) :
    IsLocalization.mk' R[T;T⁻¹] p (⟨Polynomial.X^n, n, rfl⟩ : Submonoid.powers (Polynomial.X : R[X])) =
      toLaurent p * LaurentPolynomial.T (-n) := by
  rw [← IsUnit.mul_left_inj (LaurentPolynomial.isUnit_T n), LaurentPolynomial.mul_T_assoc, neg_add_cancel, LaurentPolynomial.T_zero, mul_one]
  exact LaurentPolynomial.mk'_mul_T p n

