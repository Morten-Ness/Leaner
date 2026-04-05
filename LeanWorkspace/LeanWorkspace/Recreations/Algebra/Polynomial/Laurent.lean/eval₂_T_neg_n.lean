import Mathlib

variable {R S : Type*}

variable [CommSemiring R] {S : Type*} [CommSemiring S] (f : R →+* S) (x : Sˣ)

theorem eval₂_T_neg_n (n : ℕ) : LaurentPolynomial.eval₂ f x (LaurentPolynomial.T (-n)) = x⁻¹ ^ n := by
  rw [← LaurentPolynomial.mk'_one_X_pow]
  unfold LaurentPolynomial.eval₂
  rw [IsLocalization.lift_mk'_spec, map_one, coe_eval₂RingHom, eval₂_X_pow, ← mul_pow,
    Units.mul_inv, one_pow]

