import Mathlib

variable (R : Type*) {M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)

variable {S : Type*} [CommSemiring S] [Algebra S R] [Module S M] [IsScalarTower S R M]

variable (R' : Type*) {M' : Type*} [CommRing R'] [AddCommGroup M'] [Module R' M']

variable [Module R M']

variable [Algebra R R'] [IsScalarTower R R' M']

theorem eval_lsingle (r : R) (i : ℕ) (m : M) : PolynomialModule.eval r (PolynomialModule.lsingle R i m) = r ^ i • m := PolynomialModule.eval_single r i m

