import Mathlib

variable (R : Type*) {M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)

variable {S : Type*} [CommSemiring S] [Algebra S R] [Module S M] [IsScalarTower S R M]

variable (R' : Type*) {M' : Type*} [CommRing R'] [AddCommGroup M'] [Module R' M']

variable [Module R M']

variable [Algebra R R'] [IsScalarTower R R' M']

theorem aeval_equivPolynomial {S : Type*} [CommRing S] [Algebra S R]
    (f : PolynomialModule S S) (x : R) :
    Polynomial.aeval x (PolynomialModule.equivPolynomial f) = PolynomialModule.eval x (PolynomialModule.map R (Algebra.linearMap S R) f) := by
  induction f using PolynomialModule.induction_linear with
  | zero => simp
  | add f g e₁ e₂ => simp_rw [map_add, e₁, e₂]
  | PolynomialModule.single i m => rw [PolynomialModule.equivPolynomial_single, aeval_monomial, mul_comm, PolynomialModule.map_single,
      Algebra.linearMap_apply, PolynomialModule.eval_single, smul_eq_mul]

