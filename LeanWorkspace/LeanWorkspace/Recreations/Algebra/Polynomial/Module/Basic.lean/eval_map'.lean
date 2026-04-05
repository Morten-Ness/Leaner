import Mathlib

variable (R : Type*) {M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)

variable {S : Type*} [CommSemiring S] [Algebra S R] [Module S M] [IsScalarTower S R M]

variable (R' : Type*) {M' : Type*} [CommRing R'] [AddCommGroup M'] [Module R' M']

variable [Module R M']

variable [Algebra R R'] [IsScalarTower R R' M']

theorem eval_map' (f : M →ₗ[R] M) (q : PolynomialModule R M) (r : R) :
    PolynomialModule.eval r (PolynomialModule.map R f q) = f (PolynomialModule.eval r q) := Polynomial.eval_map R f q r

